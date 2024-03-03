#ifndef LOOP_H
#define LOOP_H
#include "blocks/block_visitor.h"
#include "blocks/basic_blocks.h"
#include "blocks/dominance.h"
#include "blocks/stmt.h"
#include <unordered_set>

namespace block {
class loop_info;
class loop {
public:
    loop(std::shared_ptr<basic_block> header): header_block(header) {}
    stmt::Ptr convert_to_ast_impl(loop_info &li, dominator_analysis &dta_, std::vector<std::pair<std::shared_ptr<basic_block>, stmt_block::Ptr>> &return_blocks, std::unordered_set<std::shared_ptr<basic_block>> &visited);

    struct loop_bounds_ {
        stmt::Ptr ind_var;
        // TODO: intial value of ind var
        stmt::Ptr steps_ind_var;
        // TODO: value of the step
        // TODO: final value of the step
        stmt::Ptr cond_ind_var;
        // TODO: direction of step
        stmt::Ptr entry_stmt;
    } loop_bounds;

    unsigned int loop_id;
    basic_block::cfg_block blocks;
    std::unordered_set<int> blocks_id_map;
    std::shared_ptr<loop> parent_loop;
    std::shared_ptr<basic_block> header_block;
    std::shared_ptr<basic_block> condition_block;
    std::shared_ptr<basic_block> unique_exit_block;
    basic_block::cfg_block loop_latch_blocks;
    basic_block::cfg_block loop_exit_blocks;
    std::vector<std::shared_ptr<loop>> subloops;
    while_stmt::Ptr structured_ast_loop;
};
void dump(loop &l);

class loop_info {
public:
    loop_info(basic_block::cfg_block ast, dominator_analysis &dt, dominator_analysis &post_dt): parent_ast(ast), dta(dt), post_dta(post_dt) {
        // TODO: Add checks to see if ast, dt and post_dt is valid
        analyze();
    }
    std::shared_ptr<loop> allocate_loop(std::shared_ptr<basic_block> header);
    stmt_block::Ptr convert_to_ast(stmt_block::Ptr ast);
    std::map<unsigned int, std::vector<int>> postorder_loops_map;
    std::map<unsigned int, std::vector<int>> preorder_loops_map;
    std::vector<std::shared_ptr<loop>> loops;
    std::vector<std::shared_ptr<loop>> top_level_loops;

private:
    basic_block::cfg_block parent_ast;
    dominator_analysis dta;
    dominator_analysis post_dta;
    std::map<int, std::shared_ptr<loop>> bb_loop_map;
    void postorder_dfs_helper(std::vector<int> &postorder_loops_map, std::vector<bool> &visited_loops, int id);
    void preorder_dfs_helper(std::vector<int> &preorder_loops_map, std::vector<bool> &visited_loops, int id);
    // discover loops during traversal of the abstract syntax tree
    void analyze();
};
} // namespace block

#endif