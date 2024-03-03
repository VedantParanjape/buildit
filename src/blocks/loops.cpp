#include "blocks/loops.h"
#include <unordered_set>
#include <algorithm>
#include <tuple>
#include <set>

namespace block {
void dump(loop &l) {
    std::cerr << "++++++ loop " << l.loop_id << " ++++++ \n";
    std::cerr << "loop headers: " << l.header_block->id << "\n";

    std::cerr << "blocks: ";
    for (auto bb: l.blocks) std::cerr << bb->id << " ";
    std::cerr << "\n";

    std::cerr << "loop latches: ";
    for (auto bb: l.loop_latch_blocks) std::cerr << bb->id << " ";
    std::cerr << "\n";
    
    std::cerr << "loop exits: ";
    for (auto bb: l.loop_exit_blocks) std::cerr << bb->id << " ";
    std::cerr << "\n";
    if (l.unique_exit_block) std::cerr << "loop unique exit block: " << l.unique_exit_block->id << "\n";

    std::cerr << "parent loop: (loop header: " << (l.parent_loop ? (int)l.parent_loop->header_block->id : -1) << ")\n";

    std::cerr << "subloops: ";
    for (auto subl: l.subloops) std::cerr << "(loop header: " << subl->header_block->id << ") ";
    std::cerr << "\n";
    std::cerr << "++++++ loop ++++++ \n";
}

// Allocates a loop object with the argument as the header block.
// Also adds the loop to the header block -> loop map
// returns the allocated loop object as a shared_ptr
std::shared_ptr<loop> loop_info::allocate_loop(std::shared_ptr<basic_block> header) {
    if (!header)
        return nullptr;

    loops.push_back(std::make_shared<loop>(header));
    bb_loop_map[header->id] = loops.back();
    return loops.back();
}

void loop_info::postorder_dfs_helper(std::vector<int> &postorder_loops_map, std::vector<bool> &visited_loops, int id) {
    for (auto subloop: loops[id]->subloops) {
        if (!visited_loops[subloop->loop_id]) {
            visited_loops[subloop->loop_id] = true;
            postorder_dfs_helper(postorder_loops_map, visited_loops, subloop->loop_id);
            postorder_loops_map.push_back(subloop->loop_id);
        }
    }
}

void loop_info::preorder_dfs_helper(std::vector<int> &preorder_loops_map, std::vector<bool> &visited_loops, int id) {
    for (auto subloop: loops[id]->subloops) {
        if (!visited_loops[subloop->loop_id]) {
            visited_loops[subloop->loop_id] = true;
            preorder_loops_map.push_back(subloop->loop_id);
            preorder_dfs_helper(preorder_loops_map, visited_loops, subloop->loop_id);
        }
    }
}

void loop_info::analyze() {
    // Do a traversal of the CFG on the postorder immediate
    // dominator map, get_postorder_idom_map retuns a list 
    // of postorder traversal of the dom tree.
    for (int idom_id: dta.get_postorder_idom_map()) {
        std::vector<int> backedges;
        int header = idom_id;

        // Check for the predecessors of each basic block.
        // If the header block dominates the predecessor,
        // it means that it is a backedge to the header block,
        // and possibly a loop backedge.
        for (auto backedge: dta.cfg_[header]->predecessor) {
            if (dta.dominates(header, backedge->id) && dta.is_reachable_from_entry(backedge->id)) {
                backedges.push_back(backedge->id);
            }
        }

        // If no backedges found for this basic block,
        // it's not a loop header, so continue.
        if (backedges.empty())
            continue;

        // Allocate a new loop object with the given
        // basic block as its header.
        std::shared_ptr<loop> new_loop = allocate_loop(dta.cfg_[header]);
        if (!new_loop)
            continue;

        int num_blocks = 0;
        int num_subloops = 0;

        // Insert the basic block objects for the backedges
        // in the worklist, we need to do this as backedges
        // vector just stores the basic block id.
        auto backedge_iter = backedges.begin();
        basic_block::cfg_block worklist(backedges.size());
        std::generate(worklist.begin(), worklist.end(), 
            [&backedge_iter, this](){
                return dta.cfg_[*(backedge_iter++)];
            });

        // Do a reverse CFG traversal to map basic blocks in this
        // loop. Process the worklist from the end, and work the way
        // back from the predecessor of the given backedge.
        while (!worklist.empty()) {
            unsigned int predecessor_bb_id = worklist.back()->id;
            worklist.pop_back();

            // Check if the pred basic block is already mapped and 
            // added to the bb_loop_map. 
            // If it is not, then add it to the bb_loop_map and add
            // the predecessor of the pred basic block to the worklist.
            // If it is, it means that this basic block has already 
            // been discovered and mapped to some other loop. We need
            // to find the outermost loop.
            auto subloop_iter = bb_loop_map.find(predecessor_bb_id);
            if (subloop_iter == bb_loop_map.end()) {
                if (!dta.is_reachable_from_entry(predecessor_bb_id))
                    continue;

                bb_loop_map[predecessor_bb_id] = new_loop;
                ++num_blocks;
                // Loop has no blocks between header and backedge
                if (predecessor_bb_id == new_loop->header_block->id)
                    continue;

                worklist.insert(worklist.end(), dta.cfg_[predecessor_bb_id]->predecessor.begin(), dta.cfg_[predecessor_bb_id]->predecessor.end());
            }
            else {
                std::shared_ptr<loop> subloop = subloop_iter->second;
                // Walk back on the subloop tree, to find out
                // the topmost parent loop.
                while (subloop->parent_loop) {
                    subloop = subloop->parent_loop;
                }

                // It is already a subloop of the current loop.
                if (subloop == new_loop)
                    continue;

                // Discovered a subloop of this current loop.
                subloop->parent_loop = new_loop;
                ++num_subloops;
                num_blocks = num_blocks + subloop->blocks.size();
                predecessor_bb_id = subloop->header_block->id;

                // predecessors that are not this loop's backedges might lead to
                // another subloop as well, so add them to the worklist.
                for (auto pred: dta.cfg_[predecessor_bb_id]->predecessor) {
                    auto loop_iter = bb_loop_map.find(pred->id);
                    // do not check if loop_iter != bb_loop_map.end(), as a results
                    // basic blocks that are not directly part of the natural loops
                    // are skipped, like loop latches.
                    if (loop_iter->second != subloop)
                        worklist.push_back(pred);
                }
            }
        }
        new_loop->subloops.reserve(num_subloops);
        new_loop->blocks.reserve(num_blocks);
        new_loop->blocks_id_map.reserve(num_blocks);
    }

    // populate all subloops and loops with blocks
    for (auto bb_id: dta.get_postorder()) {
        auto subloop_iter = bb_loop_map.find(bb_id);
        std::shared_ptr<loop> subloop = nullptr;
        if (subloop_iter != bb_loop_map.end() && (subloop = subloop_iter->second) && dta.cfg_[bb_id] == subloop->header_block) {
            // check if it is the outermost loop
            if (subloop->parent_loop != nullptr) {
                subloop->parent_loop->subloops.push_back(subloop);
            }
            else {
                top_level_loops.push_back(subloop);
            }

            std::reverse(subloop->blocks.begin(), subloop->blocks.end());
            std::reverse(subloop->subloops.begin(), subloop->subloops.end());

            subloop = subloop->parent_loop;
        }

        while (subloop) {
            subloop->blocks.push_back(dta.cfg_[bb_id]);
            subloop->blocks_id_map.insert(dta.cfg_[bb_id]->id);
            subloop = subloop->parent_loop;
        }
    }

    // Populate the loop latches
    for (auto loop: loops) {
        if (!loop->header_block)
            continue;

        std::shared_ptr<basic_block> header = loop->header_block;
        for (auto children: header->predecessor) {
            if (loop->blocks_id_map.count(children->id)) {
                loop->loop_latch_blocks.push_back(children);
            }
        }
    }

    // Populate the loop exits
    for (auto loop: loops) {
        if (!loop->header_block)
            continue;
        
        for (auto bb: loop->blocks) {
            for (auto children: bb->successor) {
                if (!loop->blocks_id_map.count(children->id) && children->id != loop->header_block->id) {
                    loop->loop_exit_blocks.push_back(bb);
                    break;
                }
            }
        }
    }

    // Update unique loop exit using post dominators
    for (auto loop: loops) {
        if (loop->loop_exit_blocks.size() == 0)
            continue;

        int unique_postdom = post_dta.get_idom(loop->loop_exit_blocks[0]->id);
        if (unique_postdom == -1)
            continue;

        bool unique_postdom_flag = true;
        for (auto exit_bb: loop->loop_exit_blocks) {
            if (post_dta.get_idom(exit_bb->id) != unique_postdom) {
                unique_postdom_flag = false;
            }
        }

        if (unique_postdom_flag)
            loop->unique_exit_block = dta.cfg_[unique_postdom];
    }

    // Populate loop condition block
    for(auto loop: loops) {
        if (!loop->header_block)
            continue;

        // this might be an unconditional loop or
        // infinite loop.
        if (loop->loop_exit_blocks.empty())
            continue;

        std::shared_ptr<basic_block> header = loop->header_block;
        assert(header->successor.size() == 1 && "loop header cannot have more than one successor");
        if (isa<if_stmt>(header->successor[0]->parent))
            loop->condition_block = header->successor[0];
    }

    // Assign id to the loops
    for (unsigned int i = 0; i < loops.size(); i++) {
        loops[i]->loop_id = i;
    }

    // build a postorder loop tree
    std::vector<bool> visited_loops(loops.size());
    visited_loops.assign(visited_loops.size(), false);
    for (auto loop: top_level_loops) {
        std::vector<int> postorder_loop_tree;
        visited_loops[loop->loop_id] = true;

        postorder_dfs_helper(postorder_loop_tree, visited_loops, loop->loop_id);
        postorder_loop_tree.push_back(loop->loop_id);
        postorder_loops_map[loop->loop_id] = postorder_loop_tree;
    }

    // build a preorder loop tree
    visited_loops.clear();
    visited_loops.assign(visited_loops.size(), false);
    for (auto loop: top_level_loops) {
        std::vector<int> preorder_loop_tree;
        visited_loops[loop->loop_id] = true;

        preorder_loop_tree.push_back(loop->loop_id);
        preorder_dfs_helper(preorder_loop_tree, visited_loops, loop->loop_id);
        preorder_loops_map[loop->loop_id] = preorder_loop_tree;
    }
}
} // namespace block
