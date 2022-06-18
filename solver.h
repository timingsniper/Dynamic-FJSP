#ifndef SOLVER_H
#define SOLVER_H

#include"cho.h"
#include"us_time_count.h"

#include<vector>
#include<queue>
#include<unordered_map>

using namespace std;

const double run_time = 150.0;//原始订单运行150秒

extern int job_count;
extern int machine_count;
extern int insert_count;
extern int ope_sum;
extern int Tabu_tenure;
extern int global_best_obj;
extern int same_pos_count;

class Solution {
public:
	vector<vector<cho>> ope_on_machine;//操作在机器序列中的位置
	vector<vector<cho>> machine_ass;//机器任务分配
	vector<int> ope_count_per_machine;//每个机器安排的任务数
	vector<vector<int>> R;//记录R值
	vector<vector<int>> Q;//记录Q值
    int makespan = 0;//记录makespan
    vector<vector<cho>> cri_block;//记录关键块
	vector<vector<int>> where_machine;
};

extern vector<vector<vector<cho>>> job,Job;
extern vector<vector<cho>>ans,tmpans;
extern vector<vector<cho>>machine;
extern vector<vector<int>> empty_QorR;

extern queue<cho> store, store1;
extern vector<cho> cur_block;

extern stop_watch record_time;

struct Hashfunc {
    size_t operator() (const vector<cho>& key) const {
        size_t ans = hash<int>()(key[0].x)^ hash<int>()(key[0].t);
        for (int i = 1; i < key.size();++i) {
            ans ^= (hash<int>()(key[i].x) ^ hash<int>()(key[i].t));
        }
        return ans;
    }
};

struct Equalfunc {
    bool operator() (const vector<cho>& a, const vector<cho>& b) const {
        bool ans = true;
        if (a.size() != b.size()) {
            return false;
        }
        for (int i = 0; i < a.size(); ++i) {
            ans = (a[i].x == b[i].x && a[i].t == b[i].t)&&ans;
        }
        return ans;
    }
};

bool my_cmp(vector<int>& a, vector<int>& b);
void print_vector(vector<vector<vector<cho>>> c);
void print_ans(vector<vector<cho>> ans);
void print_machine(vector<vector<cho>> machine);
void Initial(Solution &S);//随机生成初始解
void caculate_makespan(Solution &S);//计算makespan,并更新R,Q以及cri_block
int caculate_d(Solution &S1, Solution & S2);//计算两个解的距离
void make_move(vector<int>& move, Solution& S);//进行移动
void Nk_nei(const vector<cho> &x,Solution& S,int i,int &best_makespan,vector<vector<int>>&best_move,
    vector<unordered_map<vector<cho>, int, Hashfunc, Equalfunc>> &Tabu_table,vector<vector<cho>> &best_pattern,
    vector<vector<cho>>& best_pattern2,vector<int> &best_move_tabu,vector<cho> &best_pattern_tabu,int& best_makespan_tabu);
void PR_make_move(Solution& S_min, vector<int>& move);
void PR(Solution &Si, Solution &Sg, Solution &S,float alpha,float beta, float gama);
void TS(Solution &S, Solution &cur);
Solution MAE(int p,Solution &S_star);
int get_ope_time(int x,int t,int m);//给定订单号x,工序号t,机器号m,求加工时间
vector<vector<cho>> caculate_ans(Solution &S);//由Solution S求出ans
vector<vector<cho>> fjsp(int job_count,int machine_count,vector<vector<vector<cho>>> job);//原始订单
vector<cho> insert(vector<vector<cho>> pans,int job_count,int machine_count,vector<vector<vector<cho>>> job,int itime);//插单,只返回新订单的安排情况

#endif