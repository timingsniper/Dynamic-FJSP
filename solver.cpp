#include"cho.h"
#include"solver.h"
#include"us_time_count.h"

#include<iostream>
#include<vector>
#include<random>
#include<algorithm>
#include<unordered_map>
#include<queue>

using namespace std;

std::random_device rd;
mt19937 gen(rd());

int job_count = 0;
int machine_count = 0;
int insert_count = 0;
int ope_sum = 0;
int Tabu_tenure = 5;
int global_best_obj = INT_MAX;
int same_pos_count = 0;

vector<vector<vector<cho>>> job,Job;
vector<vector<cho>> ans,tmpans;
vector<vector<cho>> machine;

vector<vector<int>> empty_QorR;
queue<cho> store, store1;
vector<vector<int>> temp_m_ass(machine_count);
vector<cho> cur_block;

stop_watch record_time;

bool my_cmp(vector<int>& a, vector<int>& b) {
    return (a[0] + a[1]) < (b[0] + b[1]);
}

void print_vector(vector<vector<vector<cho>>> c)
{
    int p=c.size();
    for(int i=0;i<p;i++)
    {
        int q=c[i].size();
        for(int j=0;j<q;j++)
        {
            int r=c[i][j].size();
            for(int k=0;k<r;k++)
            {
                printf("%d %d ",c[i][j][k].x,c[i][j][k].t);
            }
            cout<<"##";
        }
        cout<<endl;
    }
}

void print_ans(vector<vector<cho>> ans){
	for(int i=0;i<ans.size();i++){
		for(int j=0;j<ans[i].size();j++){
			printf("machine = %d,start time= %d\n",ans[i][j].x,ans[i][j].t);
		}
		puts("");
	}
}

void print_machine(vector<vector<cho>> machine){
    for(int i=1;i<machine.size();i++){
		for(int j=0;j<machine[i].size();j++){
			cout<<machine[i][j].x<<' '<<machine[i][j].t<<'#';
		}
		cout<<endl;
	}
}

void Initial(Solution &S) {
    S.ope_on_machine.resize(job_count);
    S.machine_ass.resize(machine_count);
    S.R.resize(job_count);
    S.Q.resize(job_count);
    S.ope_count_per_machine.reserve(machine_count);
    S.where_machine.resize(job_count);
    vector<cho> arrive_job_site(job_count);
    for (int i = 0; i < job_count; i++) {
        arrive_job_site[i] = {i,0};
        S.ope_on_machine[i].resize(job[i].size());
        S.R[i].resize(job[i].size(), -1);
        S.Q[i].resize(job[i].size(), -1);
        S.where_machine[i].resize(job[i].size(), -1);
    }
    int count = 0;
    int cur_size = job_count-1;
    while (count < ope_sum) {
        uniform_int_distribution<> dis1(0, cur_size);
        int f1 = dis1(gen);
        int f = arrive_job_site[f1].x;
        int s = arrive_job_site[f1].t;
        uniform_int_distribution<> dis(0, job[f][s].size() - 1);
        int t = dis(gen);
        S.machine_ass[job[f][s][t].x].push_back({f,s});//可行
        S.where_machine[f][s] = t;
        int t1 = S.machine_ass[job[f][s][t].x].size() - 1;
        S.ope_on_machine[f][s] = { job[f][s][t].x,t1 };
        ++count;
        ++arrive_job_site[f1].t;
        if (arrive_job_site[f1].t>=job[f].size()) {
            if (f1 != cur_size) {
                cho temp = arrive_job_site[cur_size];
                arrive_job_site[cur_size] = arrive_job_site[f1];
                arrive_job_site[f1] = temp;
            }
            --cur_size;//某个订单已经安排完成
        }
    }
    for (const auto& x : S.machine_ass) {
        S.ope_count_per_machine.push_back(x.size());
    }
}

void caculate_makespan(Solution &S){
    S.cri_block.clear();
    S.makespan = 0;
	S.Q.assign(empty_QorR.begin(), empty_QorR.end());
	S.R.assign(empty_QorR.begin(), empty_QorR.end());
    S.ope_count_per_machine.assign(machine_count, 0);
    for (int i = 0; i < machine_count; ++i) {
        S.ope_count_per_machine[i] = S.machine_ass[i].size();
    }
    for (int i = 0; i < job_count; ++i) {
        if (S.ope_on_machine[i][0].t == 0) {
            S.R[i][0] = 0;
            store.push({ i,0 });
        }
		int ss2 = job[i].size() - 1;
		cho ss1 = S.ope_on_machine[i][ss2];
        if (ss1.t ==S.machine_ass[ss1.x].size() - 1) {
            S.Q[i][ss2] = 0;
            store1.push({ i,ss2 });
        }
    }
    cho temp;
	stop_watch s;
	s.start();
	int sum = 0;
    while (!store.empty()) {
        temp = store.front();
        store.pop();
        int t1 = temp.x;
        int t2 = temp.t + 1;
        if (t2 < job[t1].size()&&S.R[t1][t2]==-1) {
            int t3 = S.ope_on_machine[t1][t2].x;
            int t4 = S.ope_on_machine[t1][t2].t;
			if (t4 == 0 || S.R[S.machine_ass[t3][t4 - 1].x][S.machine_ass[t3][t4 - 1].t] != -1) {
				if (t4 == 0) {
					S.R[t1][t2] = S.R[t1][temp.t] + job[t1][temp.t][S.where_machine[t1][temp.t]].t;
				}
				else {
					int s1 = S.machine_ass[t3][t4 - 1].x;
					int s2 = S.machine_ass[t3][t4 - 1].t;
					int s3 = S.R[t1][temp.t] + job[t1][temp.t][S.where_machine[t1][temp.t]].t;
					int s4 = S.R[s1][s2] + job[s1][s2][S.where_machine[s1][s2]].t;
					if (s3 > s4) {
						S.R[t1][t2] = s3;
					}
					else {
						S.R[t1][t2] = s4;
					}
				}
				store.push({ t1,t2 });
			}
        }
        int t3 = S.ope_on_machine[t1][temp.t].x;
        int t4 = S.ope_on_machine[t1][temp.t].t;
        if (t4 != S.machine_ass[t3].size() - 1&& S.R[S.machine_ass[t3][t4+1].x][S.machine_ass[t3][t4 + 1].t] == -1) {
            int t5 = S.machine_ass[t3][t4 + 1].x;
            int t6 = S.machine_ass[t3][t4 + 1].t;
			if (t6 == 0 || S.R[t5][t6 - 1] != -1) {
				if (t6 == 0) {
					S.R[t5][t6] = S.R[t1][temp.t] + job[t1][temp.t][S.where_machine[t1][temp.t]].t;
				}
				else {
					int s3 = S.R[t1][temp.t] + job[t1][temp.t][S.where_machine[t1][temp.t]].t;
					int s4 = S.R[t5][t6 - 1] + job[t5][t6 - 1][S.where_machine[t5][t6 - 1]].t;
					if (s3 > s4) {
						S.R[t5][t6] = s3;
					}
					else {
						S.R[t5][t6] = s4;
					}
				}
				store.push({ t5,t6 });
			}
        }
    }
    while (!store1.empty()) {
		++sum;
        temp = store1.front();
        store1.pop();
        int t1 = temp.x;
        int t2 = temp.t - 1;
        if (temp.t != 0) {
            if (S.Q[t1][t2] == -1) {
                int t3 = S.ope_on_machine[t1][t2].x;
                int t4 = S.ope_on_machine[t1][t2].t;
				if (t4 == S.ope_count_per_machine[t3] - 1 || S.Q[S.machine_ass[t3][t4 + 1].x][S.machine_ass[t3][t4 + 1].t] != -1) {
					if (t4 == S.ope_count_per_machine[t3] - 1) {
						S.Q[t1][t2] = S.Q[t1][temp.t] + job[t1][temp.t][S.where_machine[t1][temp.t]].t;
					}
					else {
						int s1 = S.machine_ass[t3][t4 + 1].x;
						int s2 = S.machine_ass[t3][t4 + 1].t;
						int s3 = S.Q[t1][temp.t] + job[t1][temp.t][S.where_machine[t1][temp.t]].t;
						int s4 = S.Q[s1][s2] + job[s1][s2][S.where_machine[s1][s2]].t;
						if (s3 > s4) {
							S.Q[t1][t2] = s3;
						}
						else {
							S.Q[t1][t2] = s4;
						}
					}
					store1.push({ t1,t2 });
				}
            }
        }
        int t3 = S.ope_on_machine[t1][temp.t].x;
        int t4 = S.ope_on_machine[t1][temp.t].t;
        if (t4 != 0) {
            int t5 = S.machine_ass[t3][t4 -1].x;
            int t6 = S.machine_ass[t3][t4 -1].t;
            if (S.Q[t5][t6] == -1) {
				if (t6 == job[t5].size() - 1 || S.Q[t5][t6 + 1] != -1) {
					if (t6 == job[t5].size() - 1) {
						S.Q[t5][t6] = S.Q[t1][temp.t] + job[t1][temp.t][S.where_machine[t1][temp.t]].t;
					}
					else {
						int s3 = S.Q[t1][temp.t] + job[t1][temp.t][S.where_machine[t1][temp.t]].t;
						int s4 = S.Q[t5][t6 + 1] + job[t5][t6 + 1][S.where_machine[t5][t6 + 1]].t;
						if (s3 > s4) {
							S.Q[t5][t6] = s3;
						}
						else {
							S.Q[t5][t6] = s4;
						}
					}
					store1.push({ t5,t6 });
				}
            }
        }
    }
    for (int i = 0; i < job_count; ++i) {
        int t = S.R[i][job[i].size() - 1] + job[i][job[i].size() - 1][S.where_machine[i][job[i].size() - 1]].t + S.Q[i][job[i].size()-1];
        if (t > S.makespan) {
            S.makespan = t;
        }
    }
	temp_m_ass.assign(machine_count, {});
    for (int i = 0; i < machine_count;++i) {
        temp_m_ass[i].resize(S.machine_ass[i].size(), 0);
    }
    for (int i = 0; i < job_count; ++i) {
        for (int j = 0; j < job[i].size(); ++j) {
            int t = S.ope_on_machine[i][j].x;
            int t1= S.ope_on_machine[i][j].t;
            if (S.R[i][j] + job[i][j][S.where_machine[i][j]].t + S.Q[i][j] == S.makespan) {
                temp_m_ass[t][t1] = 1;
            }
        }
    }
    for (int i = 0; i < machine_count; ++i) {
        cur_block.clear();
        for (int j = 0; j < S.machine_ass[i].size(); ++j) {
            if (temp_m_ass[i][j] == 0) {
                if (cur_block.size() != 0) {
                    S.cri_block.push_back(cur_block);
                    cur_block.clear();
                }
            }
            else {
                cur_block.push_back({ S.machine_ass[i][j].x,S.machine_ass[i][j].t });
                if (j == S.machine_ass[i].size() - 1) {
                    S.cri_block.push_back(cur_block);
                }
            }
        }
    }
}

int caculate_d(Solution &S1, Solution & S2) {
    int d_sum = 0;
	same_pos_count = 0;
    for (int i = 0; i < job_count; i++) {
        for (int j = 0; j < job[i].size(); j++) {
            if (S1.ope_on_machine[i][j].x == S2.ope_on_machine[i][j].x) {//同一机器
				if (S1.ope_on_machine[i][j].t == S2.ope_on_machine[i][j].t)
					++same_pos_count;
                d_sum += abs(S1.ope_on_machine[i][j].t - S2.ope_on_machine[i][j].t);
            }
            else {//不同机器
                int t1 = S1.ope_on_machine[i][j].t + S2.ope_on_machine[i][j].t;
                int t2 = S1.ope_on_machine[i][j].x;
                int t3 = S2.ope_on_machine[i][j].x;
                int t4 = S1.machine_ass[t2].size() -1 - S1.ope_on_machine[i][j].t + 
                    S2.machine_ass[t3].size()-1 - S1.ope_on_machine[i][j].t;
                d_sum += t1 > t4 ? t1 : t4;
            }
        }
    }
    return d_sum;
}

void make_move(vector<int>& move, Solution& S) {
    int ai = move[0], aj = move[1], bi = move[2], bj = move[3];
    if (move[4] == 0) {
        //cout << "前插" << endl;
        int m1 = S.ope_on_machine[ai][aj].x;
        int m2 = -1;
        if(move[2]==-2){
            m2 = move[3];
        }
        else {
            m2 = S.ope_on_machine[bi][bj].x;
        }
        S.machine_ass[m1].erase(S.machine_ass[m1].begin() + S.ope_on_machine[ai][aj].t); 
        if(m1==m2)
            S.machine_ass[m2].insert(S.machine_ass[m2].begin() + (S.ope_on_machine[bi][bj].t<0?0:
                S.ope_on_machine[bi][bj].t), {ai,aj});
        else {
            if (m2 == -2) {
                S.machine_ass[m2].insert(S.machine_ass[m2].begin(), { ai,aj });
            }
            else {
                S.machine_ass[m2].insert(S.machine_ass[m2].begin() + S.ope_on_machine[bi][bj].t, { ai,aj });
            }
        }
        for (int i = 0; i < S.machine_ass[m1].size(); ++i) {
            int t1 = S.machine_ass[m1][i].x, t2 = S.machine_ass[m1][i].t;
            S.ope_on_machine[t1][t2] = { m1,i };
        }
        if (m2 != m1) {
            S.ope_count_per_machine[m1] -= 1;
            S.ope_count_per_machine[m2] += 1;
            int t = 0;
            for (int i = 0; i < job[ai][aj].size();++i) {
                if (job[ai][aj][i].x == m2) {
                    t = i;
                    break;
                }
            }
            S.where_machine[ai][aj] = t;
            for (int i = 0; i < S.machine_ass[m2].size(); ++i) {
                int t1 = S.machine_ass[m2][i].x, t2 = S.machine_ass[m2][i].t;
                S.ope_on_machine[t1][t2] = { m2,i };
            }
        }
    }
    else {
        //cout << "后插" << endl;
        int m1 = S.ope_on_machine[ai][aj].x;
        int m2 = -1;
        if (move[2] == -2) {
            m2 = move[3];
        }
        else {
            m2 = S.ope_on_machine[bi][bj].x;
        }
        S.machine_ass[m1].erase(S.machine_ass[m1].begin() + S.ope_on_machine[ai][aj].t);
        if(m1==m2)
            S.machine_ass[m2].insert(S.machine_ass[m2].begin() + S.ope_on_machine[bi][bj].t, { ai,aj });
        else {
            if (move[2] == -2) {
                S.machine_ass[m2].insert(S.machine_ass[m2].begin(), { ai,aj });
            }
            else {
                S.machine_ass[m2].insert(S.machine_ass[m2].begin() + (S.ope_on_machine[bi][bj].t + 1 >=
                    S.machine_ass[m2].size() ? S.machine_ass[m2].size() : S.ope_on_machine[bi][bj].t + 1), { ai,aj });
            }
        }
        for (int i = 0; i < S.machine_ass[m1].size(); ++i) {
            int t1 = S.machine_ass[m1][i].x, t2 = S.machine_ass[m1][i].t;
            S.ope_on_machine[t1][t2] = { m1,i };
        }
        if (m2 != m1) {
            S.ope_count_per_machine[m1] -= 1;
            S.ope_count_per_machine[m2] += 1;
            int t = 0;
            for (int i = 0; i < job[ai][aj].size(); ++i) {
                if (job[ai][aj][i].x == m2) {
                    t = i;
                    break;
                }
            }
            S.where_machine[ai][aj] = t;
            for (int i = 0; i < S.machine_ass[m2].size(); ++i) {
                int t1 = S.machine_ass[m2][i].x, t2 = S.machine_ass[m2][i].t;
                S.ope_on_machine[t1][t2] = { m2,i };
            }
        }
    }
    caculate_makespan(S);
}

void Nk_nei(const vector<cho> &x,Solution& S,int i,int &best_makespan,vector<vector<int>>&best_move,
    vector<unordered_map<vector<cho>, int, Hashfunc, Equalfunc>> &Tabu_table,vector<vector<cho>> &best_pattern,
    vector<vector<cho>>& best_pattern2,vector<int> &best_move_tabu,vector<cho> &best_pattern_tabu,int& best_makespan_tabu) {
    int machine_num = S.ope_on_machine[x[i].x][x[i].t].x;
    int t1 = x[i].x;
    int t2 = x[i].t;
    vector<cho> bf_changed;
    vector<cho> af_changed;
	vector<cho> ori_ma_bf_changed(S.machine_ass[machine_num]);
	vector<cho> ori_ma_af_changed(ori_ma_bf_changed);
    ori_ma_af_changed.erase(ori_ma_af_changed.begin() + S.ope_on_machine[t1][t2].t);
    if (ori_ma_af_changed.size() == 0) {
        if (S.machine_ass[machine_num].size() == 1)
            ori_ma_af_changed = { {-1,-1} };
        else {
            ori_ma_af_changed = { {-2,-2} };
        }
    }
	if (Tabu_table[machine_num].find(ori_ma_af_changed) != Tabu_table[machine_num].end())
		return;
    for (const auto& y : job[t1][t2]) {
        if (y.x == machine_num)
            continue;
        int cur_machine = y.x;
        if (S.machine_ass[cur_machine].size() == 0) {
            bf_changed.assign(1, { -1,-1 });
            af_changed.assign(1, { t1,t2 });
            int temp_Ri = t2 == 0 ? 0 : S.R[t1][t2 - 1] + job[t1][t2 - 1][S.where_machine[t1][t2 - 1]].t;
            int temp_Qi = t2 == job[t1].size() - 1 ? 0 : S.Q[t1][t2 + 1] + job[t1][t2 + 1][S.where_machine[t1][t2 + 1]].t;
            int temp_makespan = temp_Ri + job[t1][t2][S.where_machine[t1][t2]].t + temp_Qi;
            if (S.makespan - job[t1][t2][S.where_machine[t1][t2]].t > temp_makespan)
                temp_makespan = S.makespan - job[t1][t2][S.where_machine[t1][t2]].t;
            if (temp_makespan < best_makespan_tabu) {
				best_makespan_tabu = temp_makespan;
                best_move_tabu = { t1,t2,-2,cur_machine,1 };
                best_pattern_tabu = ori_ma_bf_changed;
            }
            if (temp_makespan <= best_makespan && Tabu_table[cur_machine].find(af_changed) == Tabu_table[cur_machine].end() 
                && Tabu_table[machine_num].find(ori_ma_af_changed) == Tabu_table[machine_num].end()) {
                if (temp_makespan == best_makespan) {
                    best_move.push_back({ t1,t2,-2,cur_machine,1 });
                    best_pattern.push_back(ori_ma_bf_changed);
                    best_pattern2.push_back(bf_changed);
                }
                else {
                    best_makespan = temp_makespan;
                    best_move.clear();
                    best_pattern.clear();
                    best_pattern2.clear();
                    best_move.push_back({ t1,t2,-2,cur_machine,1 });
                    best_pattern.push_back(ori_ma_bf_changed);
                    best_pattern2.push_back(bf_changed);
                }
            }
            continue;
        }
		bf_changed = S.machine_ass[cur_machine];
        for (int j = 0; j < S.machine_ass[cur_machine].size() - 1; ++j) {
            int ai = S.machine_ass[cur_machine][j].x;
            int aj = S.machine_ass[cur_machine][j].t;
            int bi = S.machine_ass[cur_machine][j + 1].x;
            int bj = S.machine_ass[cur_machine][j + 1].t;
            af_changed = bf_changed;
            af_changed.insert(af_changed.begin()+(j+1), { t1,t2 });
            if ((t2 == job[t1].size() - 1 || ((ai!=t1||aj!=t2+1)&&S.Q[ai][aj] >= S.Q[t1][t2 + 1])) &&
                (t2 == 0 || ((bi!=t1||bj!=t2-1)&&S.Q[t1][t2 - 1] >= S.Q[bi][bj]))) {
                int temp_Ri = t2 == 0 ? S.R[ai][aj] + job[ai][aj][S.where_machine[ai][aj]].t :
                    max(S.R[t1][t2 - 1] + job[t1][t2 - 1][S.where_machine[t1][t2 - 1]].t,
                        S.R[ai][aj] + job[ai][aj][S.where_machine[ai][aj]].t);
                int temp_Qi = t2 == job[t1].size() - 1 ? S.Q[bi][bj] + job[bi][bj][S.where_machine[bi][bj]].t :
                    max(S.Q[t1][t2 + 1] + job[t1][t2 + 1][S.where_machine[t1][t2 + 1]].t,
                        S.Q[bi][bj] + job[bi][bj][S.where_machine[bi][bj]].t);
                int temp_makespan = temp_Ri + job[t1][t2][S.where_machine[t1][t2]].t + temp_Qi;
                if (S.makespan - job[t1][t2][S.where_machine[t1][t2]].t > temp_makespan)
                    temp_makespan = S.makespan - job[t1][t2][S.where_machine[t1][t2]].t;
                if (temp_makespan < best_makespan_tabu) {
					best_makespan_tabu = temp_makespan;
                    best_move_tabu = { t1,t2,ai,aj,1 };
                    best_pattern_tabu = ori_ma_bf_changed;
                }
                if (temp_makespan <= best_makespan && Tabu_table[cur_machine].find(af_changed) == Tabu_table[cur_machine].end()
                    && Tabu_table[machine_num].find(ori_ma_af_changed) == Tabu_table[machine_num].end()) {
                    if (temp_makespan == best_makespan) {
                        best_move.push_back({ t1,t2,ai,aj,1 });
                        best_pattern.push_back(ori_ma_bf_changed);
                        best_pattern2.push_back(bf_changed);
                    }
                    else {
                        best_makespan = temp_makespan;
                        best_move.clear();
                        best_pattern.clear();
                        best_pattern2.clear();
                        best_move.push_back({ t1,t2,ai,aj,1 });
                        best_pattern.push_back(ori_ma_bf_changed);
                        best_pattern2.push_back(bf_changed);
                    }
                }
            }
        }
        int firsti = S.machine_ass[cur_machine][0].x;
        int firstj = S.machine_ass[cur_machine][0].t;
        int lasti = S.machine_ass[cur_machine][S.machine_ass[cur_machine].size() - 1].x;
        int lastj = S.machine_ass[cur_machine][S.machine_ass[cur_machine].size() - 1].t;
        int last = S.machine_ass[cur_machine].size() - 1;
        if (t2 == 0 || ((firsti!=t1||firstj!=t2-1)&&S.Q[t1][t2 - 1] >= S.Q[firsti][firstj])) {
            int temp_Ri = t2 == 0 ? 0 : S.R[t1][t2 - 1] + job[t1][t2 - 1][S.where_machine[t1][t2 - 1]].t;
            int temp_Qi = t2 == job[t1].size() - 1 ? S.Q[firsti][firstj] + job[firsti][firstj][S.where_machine[firsti][firstj]].t :
                max(S.Q[t1][t2 + 1] + job[t1][t2 + 1][S.where_machine[t1][t2 + 1]].t,
                    S.Q[firsti][firstj] + job[firsti][firstj][S.where_machine[firsti][firstj]].t);
            int temp_makespan = temp_Ri + job[t1][t2][S.where_machine[t1][t2]].t + temp_Qi;
            af_changed = bf_changed;
            af_changed.insert(af_changed.begin(), { t1,t2 });
            if (S.makespan - job[t1][t2][S.where_machine[t1][t2]].t > temp_makespan)
                temp_makespan = S.makespan - job[t1][t2][S.where_machine[t1][t2]].t;
            if (temp_makespan < best_makespan_tabu) {
				best_makespan_tabu = temp_makespan;
                best_move_tabu = { t1,t2,firsti,firstj,0 };
                best_pattern_tabu = ori_ma_bf_changed;
            }
            if (temp_makespan <= best_makespan&&Tabu_table[cur_machine].find(af_changed)==Tabu_table[cur_machine].end()
                &&Tabu_table[machine_num].find(ori_ma_af_changed)==Tabu_table[machine_num].end()) {
                if (temp_makespan == best_makespan) {
                    best_move.push_back({ t1,t2,firsti,firstj,0 });
                    best_pattern.push_back(ori_ma_bf_changed);
                    best_pattern2.push_back(bf_changed);
                }
                else {
                    best_makespan = temp_makespan;
                    best_move.clear();
                    best_pattern.clear();
                    best_pattern2.clear();
                    best_move.push_back({ t1,t2,firsti,firstj,0 });
                    best_pattern.push_back(ori_ma_bf_changed);
                    best_pattern2.push_back(bf_changed);
                }
            }
        }
        if (t2 == job[t1].size() - 1 || ((lasti!=t1||lastj!=t2+1)&&S.Q[lasti][lastj] >= S.Q[t1][t2 + 1])) {
            int temp_Ri = t2 == 0 ? S.R[lasti][lastj] + job[lasti][lastj][S.where_machine[lasti][lastj]].t :
                max(S.R[t1][t2 - 1] + job[t1][t2 - 1][S.where_machine[t1][t2 - 1]].t,
                    S.R[lasti][lastj] + job[lasti][lastj][S.where_machine[lasti][lastj]].t);
            int temp_Qi = t2 == job[t1].size() - 1 ? 0 : S.Q[t1][t2 + 1] + job[t1][t2 + 1][S.where_machine[t1][t2 + 1]].t;
            int temp_makespan = temp_Ri + job[t1][t2][S.where_machine[t1][t2]].t + temp_Qi;
            af_changed = bf_changed;
            af_changed.insert(af_changed.end(), { t1,t2 });
            if (S.makespan - job[t1][t2][S.where_machine[t1][t2]].t > temp_makespan)
                temp_makespan = S.makespan - job[t1][t2][S.where_machine[t1][t2]].t;
            if (temp_makespan < best_makespan_tabu) {
				best_makespan_tabu = temp_makespan;
                best_move_tabu = { t1,t2,lasti,lastj,1 };
                best_pattern_tabu = ori_ma_bf_changed;
            }
            if (temp_makespan <= best_makespan&& Tabu_table[cur_machine].find(af_changed) == Tabu_table[cur_machine].end()
                &&Tabu_table[machine_num].find(ori_ma_af_changed) == Tabu_table[machine_num].end()) {
                if (temp_makespan == best_makespan) {
                    best_move.push_back({ t1,t2,lasti,lastj,1 });
                    best_pattern.push_back(ori_ma_bf_changed);
                    best_pattern2.push_back(bf_changed);
                }
                else {
                    best_makespan = temp_makespan;
                    best_move.clear();
                    best_pattern.clear();
                    best_pattern2.clear();
                    best_move.push_back({ t1,t2,lasti,lastj,1 });
                    best_pattern.push_back(ori_ma_bf_changed);
                    best_pattern2.push_back(bf_changed);
                }
            }
        }
    }
}

void PR_make_move(Solution& S_min, vector<int>& move) {
    int i = move[0], j = move[1];
    int t1 = S_min.ope_on_machine[i][j].x;
    int t3 = S_min.ope_on_machine[i][j].t;
    int t2 = move[2];
    S_min.machine_ass[t1].erase(S_min.machine_ass[t1].begin() + t3);
    S_min.machine_ass[t2].insert(S_min.machine_ass[t2].begin() + move[3], {i,j});
    if (t1 == t2) {
        for (int k = 0; k < S_min.machine_ass[t1].size(); ++k) {
            auto x = S_min.machine_ass[t1][k];
            S_min.ope_on_machine[x.x][x.t] = { t1,k };
        }
    }
    else {
        int t = -1;
        for (int k = 0; k < job[i][j].size(); ++k) {
            if (job[i][j][k].x == t2) { 
                t = k;
                break;
            }
        }
        S_min.where_machine[i][j] = t;
        for (int k = 0; k < S_min.machine_ass[t1].size();++k) {
            auto x = S_min.machine_ass[t1][k];
            S_min.ope_on_machine[x.x][x.t] = { t1,k };
        }
        for (int k = 0; k < S_min.machine_ass[t2].size(); ++k) {
            auto x = S_min.machine_ass[t2][k];
            S_min.ope_on_machine[x.x][x.t] = { t2,k };
        }
    }
}

void PR(Solution &Si, Solution &Sg, Solution &S,float alpha,float beta, float gama) {
    Solution S_cur = Si;
    vector<Solution> path_set;
    vector<Solution> N;
	N.reserve(ope_sum);
	path_set.reserve(100);
    vector<int> d_record;
    vector<int> obj_record;
    vector<int> obj_re_pathset;
	obj_re_pathset.reserve(100);
    int d_initial = caculate_d(Si, Sg);
    int cur_d = d_initial;
    caculate_makespan(S_cur);
    int iter = 0;
    Solution S_min;
    vector<cho> temp_ma_ass;
    vector<vector<int>> best_move;
    best_move.reserve(ope_sum);
    while (cur_d > alpha * d_initial) {
        if (iter > 100)
            break;
        int temp_d = cur_d;
        int start_size = N.size();
        for (int i = 0; i < job_count; ++i) {
            for (int j = 0; j < job[i].size(); ++j) {
                int min_d = INT_MAX;
                best_move.clear();
                temp_ma_ass = S_cur.machine_ass[S_cur.ope_on_machine[i][j].x];
                temp_ma_ass.erase(temp_ma_ass.begin() + S_cur.ope_on_machine[i][j].t);
                if (S_cur.ope_on_machine[i][j].x != Sg.ope_on_machine[i][j].x) {//改变机器
                    int t1 = S_cur.ope_on_machine[i][j].x;//待更新死锁检查
                    int t3 = S_cur.ope_on_machine[i][j].t;
                    int t2 = Sg.ope_on_machine[i][j].x;
                    int size = S_cur.machine_ass[t2].size();
                    for (int k = 0; k <=size; ++k) {
                        int ai, aj;
                        int bi, bj;
                        bool flag = false;
                        if (k == 0) {
                            if (size > 0) {
                                ai = S_cur.machine_ass[t2][k].x;
                                aj = S_cur.machine_ass[t2][k].t;
                                flag = j == 0 || (S_cur.Q[i][j - 1] >= S_cur.Q[ai][aj]&&(!(ai==i&&aj==j-1)));
                            }
                            else {
                                flag = true;
                            }
                        }
                        else {
                            if (k == size) {
                                bi = S_cur.machine_ass[t2][k-1].x;
                                bj = S_cur.machine_ass[t2][k-1].t;
                                flag = j == job[i].size() - 1 || ((!(bi==i&&bj==j+1))&&S_cur.Q[bi][bj] >= S_cur.Q[i][j + 1]);
                            }
                            else {
                                ai = S_cur.machine_ass[t2][k-1].x;
                                aj = S_cur.machine_ass[t2][k-1].t;
                                bi = S_cur.machine_ass[t2][k].x;
                                bj = S_cur.machine_ass[t2][k].t;
                                flag = (j == 0 || (S_cur.Q[i][j - 1] >= S_cur.Q[bi][bj] && (!(bi == i && bj == j - 1)))) && 
                                    (j == job[i].size() - 1 || ((!(ai == i && aj == j + 1)) && S_cur.Q[ai][aj] >= S_cur.Q[i][j + 1]));
                            }
                        }
                        if (flag) {
                            int temp_d = abs(k - Sg.ope_on_machine[i][j].t);
							if (temp_d == min_d) {
								best_move.push_back({ i,j,t2,k });
							}
							if(temp_d<min_d) {
								min_d = temp_d;
								best_move.clear();
								best_move.push_back({ i,j,t2,k });
							}
                                
                        }
                    }
                    
                }
                else {//改变位置
                    if (S_cur.ope_on_machine[i][j].t != Sg.ope_on_machine[i][j].t) {
                        int t1 = S_cur.ope_on_machine[i][j].x;
                        int t2 = S_cur.ope_on_machine[i][j].t;
                        int size = temp_ma_ass.size();
                        for (int k = 0; k <=size; ++k) {
                            if (k == t2)
                                continue;
                            int ai, aj;
                            int bi, bj;
                            bool flag = false;
                            if (k == 0) {
                                if (size > 0) {
                                    ai = temp_ma_ass[k].x;
                                    aj = temp_ma_ass[k].t;
                                    flag = j == 0 || (S_cur.Q[i][j - 1] >= S_cur.Q[ai][aj] && (!(ai == i && aj == j - 1)));
                                }
                                else {
                                    flag = true;
                                }
                            }
                            else {
                                if (k == size) {
                                    bi = temp_ma_ass[k - 1].x;
                                    bj = temp_ma_ass[k - 1].t;
                                    flag = j == job[i].size() - 1 || ((!(bi == i && bj == j + 1)) && S_cur.Q[bi][bj] >= S_cur.Q[i][j + 1]);
                                }
                                else {
                                    ai = temp_ma_ass[k - 1].x;
                                    aj = temp_ma_ass[k - 1].t;
                                    bi = temp_ma_ass[k].x;
                                    bj = temp_ma_ass[k].t;
                                    flag = (j == 0 || (S_cur.Q[i][j - 1] >= S_cur.Q[bi][bj] && (!(bi == i && bj == j - 1)))) &&
                                        (j == job[i].size() - 1 || ((!(ai == i && aj == j + 1)) && S_cur.Q[ai][aj] >= S_cur.Q[i][j + 1]));
                                }
                            }
                            if (flag) {
                                int temp_d = abs(k - Sg.ope_on_machine[i][j].t);
								if (temp_d == min_d) {
									best_move.push_back({ i,j,t1,k });
								}
								if(temp_d<min_d){
									min_d = temp_d;
									best_move.clear();
									best_move.push_back({ i,j,t1,k });
								}

                            }
                        }
                    }
                }
                if (best_move.size() != 0) {
                    S_min.machine_ass = S_cur.machine_ass;
                    S_min.ope_on_machine = S_cur.ope_on_machine;
                    S_min.where_machine = S_cur.where_machine;
                    uniform_int_distribution<> dis(0, best_move.size() - 1);
                    int choose = dis(gen);
                    PR_make_move(S_min, best_move[choose]);
                    N.push_back(S_min);
                }
            }
        }
        int N_size = N.size();
        for (auto it = N.begin(); it != N.end();) {
            int t = caculate_d((*it), Sg);
            if (t > cur_d) {
                it = N.erase(it);
            }
            else {
                d_record.push_back(t);
                caculate_makespan((*it));
                obj_record.push_back((*it).makespan);
                ++it;
            }
        }
        N_size = N.size();
        vector<vector<int>> index_Dis_Obj(N.size(),vector<int>(2,0));
        for (int i = 0; i < N_size; ++i) {
            for (int j = 0; j < N_size; ++j) {
                if (j != i) {
                    if (d_record[j] < d_record[i])
                        ++index_Dis_Obj[i][0];
                    if (obj_record[j] < obj_record[i])
                        ++index_Dis_Obj[i][1];
                }
            }
        }
        sort(index_Dis_Obj.begin(), index_Dis_Obj.end(), my_cmp);
        uniform_int_distribution<> dis(0, gama<(N_size-1)?gama:N_size-1);
        int k = dis(gen);
        S_cur = N[k];
        cur_d = d_record[k];
        if (cur_d == temp_d)
            ++iter;
        else {
            iter = 0;
        }
        if (d_record[k] < beta * d_initial) {
            path_set.push_back(S_cur);
            obj_re_pathset.push_back(obj_record[k]);
        }
        N.clear();
        obj_record.clear();
        d_record.clear();
    }
    int min_i = 0;
    int min_obj = INT_MAX;
    for (int i = 0; i < path_set.size(); ++i) {
        if (obj_re_pathset[i] < min_obj) {
            min_i = i;
            min_obj = obj_re_pathset[i];
        }
    }
    if (path_set.size() == 0) {
        S = S_cur;
    }
    else {
        S = path_set[min_i];
    }
    return ;
}

void TS(Solution &S, Solution &cur) {
    vector<unordered_map<vector<cho>,int,Hashfunc,Equalfunc>> Tabu_table(machine_count);
    int obj_best=S.makespan;
    int iter = 0;
    vector<int> R_temp;
    vector<int> Q_temp;
    vector<cho> temp;
    vector<cho> ori_ma_bf_changed;
    vector<cho> ori_ma_af_changed;
    vector<vector<int>> best_move;//得记录多个相等makespan的动作
    best_move.reserve(ope_sum);
    vector<vector<cho>> best_pattern;
    best_pattern.reserve(ope_sum);
    vector<vector<cho>> best_pattern2;
    best_pattern2.reserve(ope_sum);
    vector<int> best_move_tabu(5, -1);
    vector<cho> best_pattern_tabu;
	int global_iter = 0;
    while (iter < 1000) {
		++global_iter;
        int best_makespan = INT_MAX;
		int best_makespan_tabu = INT_MAX;
        best_move.clear();
        best_pattern.clear();
        best_pattern2.clear();
        best_move_tabu.assign(5, -1);
        best_pattern_tabu.clear();
        for (const auto& x : S.cri_block) {
            if (x.size() > 1) {
                for (int i = 0; i < x.size(); ++i) {
                    int machine_num = S.ope_on_machine[x[i].x][x[i].t].x;
					ori_ma_bf_changed = S.machine_ass[machine_num];
                    if (i == 0) {
                        int t1 = x[i].x;
                        int t2 = x[i].t;
                        for (int j = i + 1; j < x.size(); ++j) {
                            if (t2 == job[t1].size() - 1 || ((x[j].x!=t1||x[j].t!=t2+1)&&S.Q[x[j].x][x[j].t] >= S.Q[t1][t2 + 1])) {
                                int cur_makespan = 0;
                                R_temp.assign(j - i + 1, -1);
                                Q_temp.assign(j - i + 1, -1);
                                temp.assign(x.begin() + (i + 1), x.begin()+(j+1));
                                temp.push_back(x[i]);
                                ori_ma_af_changed = ori_ma_bf_changed;
                                ori_ma_af_changed.erase(ori_ma_af_changed.begin() + S.ope_on_machine[t1][t2].t);
                                ori_ma_af_changed.insert(ori_ma_af_changed.begin() + (S.ope_on_machine[t1][t2].t+j - i), {t1,t2});
                                int t3 = x[i + 1].x;
                                int t4 = x[i + 1].t;
                                if (S.ope_on_machine[x[i].x][x[i].t].t == 0) {//R[L1]
                                    R_temp[0] = t4 == 0 ? 0 : S.R[t3][t4 - 1] +
                                        job[t3][t4 - 1][S.where_machine[t3][t4 - 1]].t;
                                }
                                else {
                                    int s2 = S.ope_on_machine[t1][t2].t;
                                    int t5 = S.machine_ass[machine_num][s2 - 1].x;
                                    int t6 = S.machine_ass[machine_num][s2 - 1].t;
                                    R_temp[0] = t4 == 0 ? S.R[t5][t6] + job[t5][t6][S.where_machine[t5][t6]].t :
                                        max(S.R[t3][t4 - 1] + job[t3][t4 - 1][S.where_machine[t3][t4 - 1]].t,
                                            S.R[t5][t6] + job[t5][t6][S.where_machine[t5][t6]].t);
                                }
                                for (int k = i + 2; k < j; ++k) {//R L2到v
                                    t3 = x[k].x;
                                    t4 = x[k].t;
                                    int t5 = x[k - 1].x, t6 = x[k - 1].t;
                                    R_temp[k - 1-i] = t4 == 0 ? R_temp[k - 2 - i]+job[t5][t6][S.where_machine[t5][t6]].t : 
                                        max(S.R[t3][t4 - 1]+job[t3][t4-1][S.where_machine[t3][t4-1]].t,
                                            R_temp[k - 2 - i] + job[t5][t6][S.where_machine[t5][t6]].t);
                                }
                                R_temp[j - i] = t2 == 0 ? R_temp[j - i - 1]+job[x[j].x][x[j].t][S.where_machine[x[j].x][x[j].t]].t : 
                                    max(S.R[t1][t2 - 1]+ job[t1][t2 - 1][S.where_machine[t1][t2 - 1]].t
                                        , R_temp[j - i - 1] + job[x[j].x][x[j].t][S.where_machine[x[j].x][x[j].t]].t);//R[u]
                                t3 = x[j].x;
                                t4 = x[j].t;
                                if (S.ope_on_machine[t3][t4].t == S.machine_ass[machine_num].size() - 1) {//Q[u]
                                    Q_temp[j - i] = t2 == job[t1].size() - 1 ? 0 : 
                                        S.Q[t1][t2 + 1]+job[t1][t2+1][S.where_machine[t1][t2+ 1]].t;
                                }
                                else {
                                    int s2 = S.ope_on_machine[t3][t4].t;
                                    int t5 = S.machine_ass[machine_num][s2+1].x;
                                    int t6 = S.machine_ass[machine_num][s2 + 1].t;
                                    Q_temp[j - i] = t2 == job[t1].size() - 1 ? S.Q[t5][t6]+job[t5][t6][S.where_machine[t5][t6]].t : 
                                        max(S.Q[t1][t2 + 1] + job[t1][t2+1][S.where_machine[t1][t2 + 1]].t,
                                            S.Q[t5][t6] + job[t5][t6][S.where_machine[t5][t6]].t);
                                }
                                //Q[v]
                                Q_temp[j - i - 1] = t4 == job[t3].size() - 1 ? Q_temp[j - i]+job[t1][t2][S.where_machine[t1][t2]].t :
                                    max(S.Q[t3][t4 + 1]+job[t3][t4+1][S.where_machine[t3][t4+1]].t,
                                        Q_temp[j - i] + job[t1][t2][S.where_machine[t1][t2]].t);
                                for (int k = j - 1; k > i; --k) {//Q[L1至Lk]
                                    int t7 = x[k].x;
                                    int t8 = x[k].t;
                                    int t9 = x[k + 1].x, t10 = x[k + 1].t;
                                    Q_temp[k - i - 1] = t8 == job[t7].size() - 1 ? Q_temp[k - i]+job[t9][t10][S.where_machine[t9][t10]].t : 
                                        max(S.Q[t7][t8 + 1]+job[t7][t8+1][S.where_machine[t7][t8+1]].t,
                                            Q_temp[k - i] + job[t9][t10][S.where_machine[t9][t10]].t);
                                }
                                for (int k = 0; k < j - i + 1; ++k) {
                                    int s1 = R_temp[k] + job[temp[k].x][temp[k].t][S.where_machine[temp[k].x][temp[k].t]].t + Q_temp[k];
                                    cur_makespan = s1 > cur_makespan ? s1 : cur_makespan;
                                }
                                if (cur_makespan < best_makespan_tabu) {
									best_makespan_tabu = cur_makespan;
                                    best_move_tabu = { { t1,t2,x[j].x,x[j].t,1 } };
									best_pattern_tabu = ori_ma_bf_changed;
                                }
                                if (cur_makespan <= best_makespan&&Tabu_table[machine_num].find(ori_ma_af_changed) == Tabu_table[machine_num].end()) {
                                    if (cur_makespan == best_makespan) {
                                        best_move.push_back({ t1,t2,x[j].x,x[j].t,1 });
                                        best_pattern.push_back(ori_ma_bf_changed);
                                        best_pattern2.push_back({});
                                    }
                                    else {
                                        best_makespan = cur_makespan;
                                        best_move.clear();
                                        best_pattern.clear();
                                        best_pattern2.clear();
                                        best_move.push_back({ t1,t2,x[j].x,x[j].t,1 });
                                        best_pattern.push_back(ori_ma_bf_changed);
                                        best_pattern2.push_back({});
                                    }
                                }
                            }
                        }
                        Nk_nei(x, S, i, best_makespan, best_move, Tabu_table, best_pattern,best_pattern2,best_move_tabu,best_pattern_tabu,best_makespan_tabu);
                        continue;
                    }
                    if (i == x.size() - 1) {
                        int t1 = x[i].x;
                        int t2 = x[i].t;          
                        for (int j = i - 1; j > 0; --j) {
                            temp.clear();
                            temp.reserve(i);
                            temp.push_back(x[i]);
                            for (int k = j; k < i; ++k) {
                                temp.push_back(x[k]);
                            }
                            int t3 = x[j].x;
                            int t4 = x[j].t;
                            if (t2 == 0 || ((t3!=t1||t4!=t2-1)&&S.Q[t1][t2 - 1] >= S.Q[t3][t4])) {
                                R_temp.assign(i - j + 1, -1);
                                Q_temp.assign(i - j + 1, -1);
								ori_ma_af_changed = ori_ma_bf_changed;
                                ori_ma_af_changed.erase(ori_ma_af_changed.begin()+ S.ope_on_machine[t1][t2].t);
                                ori_ma_af_changed.insert(ori_ma_af_changed.begin()+ S.ope_on_machine[t3][t4].t, { t1,t2 });
                                if (t2 == 0 && S.ope_on_machine[t3][t4].t == 0) {
                                    R_temp[0] = 0;
                                }
                                else {
                                    if (t2 == 0) {
                                        int s2 = S.ope_on_machine[t3][t4].t;
                                        int t5 = S.machine_ass[machine_num][s2- 1].x;
                                        int t6 = S.machine_ass[machine_num][s2 - 1].t;
                                        R_temp[0] = S.R[t5][t6] + job[t5][t6][S.where_machine[t5][t6]].t;
                                    }
                                    else {
                                        if (S.ope_on_machine[t3][t4].t == 0) {
                                            R_temp[0] = S.R[t1][t2 - 1] + job[t1][t2 - 1][S.where_machine[t1][t2 - 1]].t;
                                        }
                                        else {
                                            int s2 = S.ope_on_machine[t3][t4].t;
                                            int t5 = S.machine_ass[machine_num][s2 - 1].x;
                                            int t6 = S.machine_ass[machine_num][s2 - 1].t;
                                            R_temp[0] =max(S.R[t5][t6] + job[t5][t6][S.where_machine[t5][t6]].t,
                                                S.R[t1][t2 - 1] + job[t1][t2 - 1][S.where_machine[t1][t2 - 1]].t);
                                        }
                                    }
                                }
                                R_temp[1] = t4 == 0 ? R_temp[0] + job[t1][t2][S.where_machine[t1][t2]].t :
                                    max(S.Q[t3][t4 - 1] + job[t3][t4 - 1][S.where_machine[t3][t4 - 1]].t,
                                        R_temp[0] + job[t1][t2][S.where_machine[t1][t2]].t);
                                for (int k = j + 1; k < i; ++k) {
                                    int t5 = x[k].x;
                                    int t6 = x[k].t;
                                    int t7 = x[k - 1].x;
                                    int t8 = x[k - 1].t;
                                    R_temp[k-j+1] = t6 == 0 ? R_temp[k-j] + job[t7][t8][S.where_machine[t7][t8]].t :
                                        max(S.R[t5][t6 - 1] + job[t5][t6-1][S.where_machine[t5][t6 - 1]].t,R_temp[k-j] + job[t7][t8][S.where_machine[t7][t8]].t);
                                }
                                t3 = x[i - 1].x;
                                t4 = x[i - 1].t;
                                if (t4 == job[t3].size() - 1 && S.ope_on_machine[t1][t2].t == S.ope_count_per_machine[machine_num] - 1) {
                                    Q_temp[i - j] = 0;
                                }
                                else {
                                    if (t4 == job[t3].size() - 1) {
                                        int s2 = S.ope_on_machine[t1][t2].t;
                                        int t5 = S.machine_ass[machine_num][s2+1].x;
                                        int t6 = S.machine_ass[machine_num][s2 + 1].t;
                                        Q_temp[i - j] = S.Q[t5][t6] + job[t5][t6][S.where_machine[t5][t6]].t;
                                    }
                                    else {
                                        if(S.ope_on_machine[t1][t2].t == S.ope_count_per_machine[machine_num] - 1)
                                            Q_temp[i - j] = S.Q[t3][t4 + 1] + job[t3][t4 + 1][S.where_machine[t3][t4+1]].t;
                                        else {
                                            int s2 = S.ope_on_machine[t1][t2].t;
                                            int t5 = S.machine_ass[machine_num][s2+1].x;
                                            int t6 = S.machine_ass[machine_num][s2 + 1].t;
                                            Q_temp[i - j] = max(S.Q[t5][t6] + job[t5][t6][S.where_machine[t5][t6]].t,
                                                Q_temp[i - j] = S.Q[t3][t4 + 1] + job[t3][t4 + 1][S.where_machine[t3][t4 + 1]].t);
                                        }
                                    }
                                }
                                for (int k = i - 2; k >=j; --k) {
                                    int t5 = x[k].x, t6 = x[k].t;
                                    int t7 = x[k + 1].x, t8 = x[k + 1].t;
                                    Q_temp[k - j + 1] = t6 == job[t5].size() - 1 ? Q_temp[k - j + 2] + job[t7][t8][S.where_machine[t7][t8]].t :
                                        max(S.Q[t5][t6 + 1] + job[t5][t6 + 1][S.where_machine[t5][t6 + 1]].t,
                                            Q_temp[k - j + 2] + job[t7][t8][S.where_machine[t7][t8]].t);
                                }
                                Q_temp[0] = t2 == job[t1].size() - 1 ? Q_temp[1] + job[x[j].x][x[j].t][S.where_machine[x[j].x][x[j].t]].t :
                                    max(S.Q[t1][t2 + 1] + job[t1][t2+1][S.where_machine[t1][t2 + 1]].t,
                                        Q_temp[1] + job[x[j].x][x[j].t][S.where_machine[x[j].x][x[j].t]].t);
                                int temp_makespan = 0;
                                for (int k = 0; k < i - j + 1; ++k) {
                                    int s = R_temp[k] + job[temp[k].x][temp[k].t][S.where_machine[temp[k].x][temp[k].t]].t + Q_temp[k];
                                    temp_makespan = s > temp_makespan ? s : temp_makespan;
                                }
                                if (temp_makespan < best_makespan_tabu) {
									best_makespan_tabu = temp_makespan;
                                    best_move_tabu = { { t1,t2,x[j].x,x[j].t,0 } };
									best_pattern_tabu = ori_ma_bf_changed;
                                }
                                if (temp_makespan < best_makespan && Tabu_table[machine_num].find(ori_ma_af_changed) == Tabu_table[machine_num].end()) {
                                    if (temp_makespan == best_makespan) {
                                        best_move.push_back({ t1,t2,x[j].x,x[j].t,0 });
                                        best_pattern.push_back(ori_ma_bf_changed);
                                        best_pattern2.push_back({});
                                    }
                                    else {
                                        best_makespan = temp_makespan;
                                        best_move.clear();
                                        best_pattern.clear();
                                        best_pattern2.clear();
                                        best_move.push_back({ t1,t2,x[j].x,x[j].t,0 });
                                        best_pattern.push_back(ori_ma_bf_changed);
                                        best_pattern2.push_back({});
                                    }
                                }
                            }
                        }
                        Nk_nei(x, S, i, best_makespan, best_move, Tabu_table, best_pattern,best_pattern2,best_move_tabu,best_pattern_tabu,best_makespan_tabu);
                        continue;
                    }
                    if (i != 0 && i != x.size() - 1) {
                        int t1 = x[i].x;
                        int t2 = x[i].t;
                        int last = x.size() - 1;
                        int s3 = x[x.size() - 1].x;
                        int s4 = x[x.size() - 1].t;
                        int s1 = x[0].x;
                        int s2 = x[0].t;
                        if (t2 == job[t1].size() - 1 || ((s3!=t1||s4!=t2+1)&&S.Q[s3][s4] >= S.Q[t1][t2 + 1])) {
                            if (i + 1 != x.size() - 1) {
                                int cur_makespan = 0;
                                temp.assign(x.begin() + (i + 1), x.end());
                                temp.push_back(x[i]);
                                R_temp.assign(last - i + 1, -1);
                                Q_temp.assign(last - i + 1, -1);
								ori_ma_af_changed = ori_ma_bf_changed;
                                ori_ma_af_changed.erase(ori_ma_af_changed.begin()+ S.ope_on_machine[t1][t2].t);
                                ori_ma_af_changed.insert(ori_ma_af_changed.begin() + (S.ope_on_machine[t1][t2].t+last - i), { t1,t2 });
                                int t3 = x[i + 1].x;
                                int t4 = x[i + 1].t;
                                if (S.ope_on_machine[x[i].x][x[i].t].t == 0) {//R[L1]
                                    R_temp[0] = t4 == 0 ? 0 : S.R[t3][t4 - 1] +
                                        job[t3][t4 - 1][S.where_machine[t3][t4 - 1]].t;
                                }
                                else {
                                    int s8 = S.ope_on_machine[x[i].x][x[i].t].t;
                                    int t5 = S.machine_ass[machine_num][s8-1].x;
                                    int t6 = S.machine_ass[machine_num][s8-1].t;
                                    R_temp[0] = t4 == 0 ? S.R[t5][t6] + job[t5][t6][S.where_machine[t5][t6]].t :
                                        max(S.R[t3][t4 - 1] + job[t3][t4 - 1][S.where_machine[t3][t4 - 1]].t,
                                            S.R[t5][t6] + job[t5][t6][S.where_machine[t5][t6]].t);
                                }
                                for (int k = i + 2; k < last; ++k) {//R L2到v
                                    t3 = x[k].x;
                                    t4 = x[k].t;
                                    int t5 = x[k - 1].x, t6 = x[k - 1].t;
                                    R_temp[k - 1 - i] = t4 == 0 ? R_temp[k - 2 - i]+ job[t5][t6][S.where_machine[t5][t6]].t :
                                        max(S.R[t3][t4 - 1]+ job[t3][t4 - 1][S.where_machine[t3][t4 - 1]].t,R_temp[k - 2 - i] + job[t5][t6][S.where_machine[t5][t6]].t);
                                }
                                R_temp[last - i] = t2 == 0 ? R_temp[last - i - 1]+job[s3][s4][S.where_machine[s3][s4]].t : 
                                    max(S.R[t1][t2 - 1]+job[t1][t2-1][S.where_machine[t1][t2-1]].t,
                                        R_temp[last - i - 1] + job[s3][s4][S.where_machine[s3][s4]].t);//R[u]
                                t3 = x[last].x;
                                t4 = x[last].t;
                                if (S.ope_on_machine[s3][s4].t == S.ope_count_per_machine[machine_num] - 1) {//Q[u]
                                    Q_temp[last - i] = t2 == job[t1].size() - 1 ? 0 : 
                                        S.Q[t1][t2 + 1]+job[t1][t2+1][S.where_machine[t1][t2+1]].t;
                                }
                                else {
                                    int s8 = S.ope_on_machine[s3][s4].t;
                                    int t5 = S.machine_ass[machine_num][s8+1].x;
                                    int t6 = S.machine_ass[machine_num][s8 + 1].t;
                                    Q_temp[last - i] = t2 == job[t1].size() - 1 ? S.Q[t5][t6]+job[t5][t6][S.where_machine[t5][t6]].t
                                        : max(S.Q[t1][t2 + 1] + job[t1][t2 + 1][S.where_machine[t1][t2 + 1]].t,
                                            S.Q[t5][t6] + job[t5][t6][S.where_machine[t5][t6]].t);
                                }
                                //Q[v]
                                Q_temp[last - i - 1] = t4 == job[t3].size() - 1 ? Q_temp[last - i]+job[t1][t2][S.where_machine[t1][t2]].t :
                                    max(S.Q[t3][t4 + 1]+job[t3][t4+1][S.where_machine[t3][t4+1]].t,
                                        Q_temp[last - i] + job[t1][t2][S.where_machine[t1][t2]].t);
                                for (int k = last - 1; k > i; --k) {//Q[L1至Lk]
                                    int t7 = x[k].x;
                                    int t8 = x[k].t;
                                    int t9 = x[k + 1].x, t10 = x[k + 1].t;
                                    Q_temp[k - i - 1] = t8 == job[t7].size() - 1 ? Q_temp[k - i]+job[t9][t10][S.where_machine[t9][t10]].t :
                                        max(S.Q[t7][t8 + 1]+job[t7][t8+1][S.where_machine[t7][t8+1]].t,
                                            Q_temp[k - i] + job[t9][t10][S.where_machine[t9][t10]].t);
                                }
                                for (int k = 0; k < last - i + 1; ++k) {
                                    int s1 = R_temp[k] + job[temp[k].x][temp[k].t][S.where_machine[temp[k].x][temp[k].t]].t + Q_temp[k];
                                    cur_makespan = s1 > cur_makespan ? s1 : cur_makespan;
                                }
                                if (cur_makespan < best_makespan_tabu) {
									best_makespan_tabu = cur_makespan;
                                    best_move_tabu = { { t1,t2,x[last].x,x[last].t,1 } };
									best_pattern_tabu = ori_ma_bf_changed;
                                }
                                if (cur_makespan < best_makespan&&Tabu_table[machine_num].find(ori_ma_af_changed) == Tabu_table[machine_num].end()) {
                                    if (cur_makespan == best_makespan) {
                                        best_move.push_back({ t1,t2,x[last].x,x[last].t,1 });
                                        best_pattern.push_back(ori_ma_bf_changed);
                                        best_pattern2.push_back({});
                                    }
                                    else {
                                        best_makespan = cur_makespan;
                                        best_move.clear();
                                        best_pattern.clear();
                                        best_pattern2.clear();
                                        best_move.push_back({ t1,t2,x[last].x,x[last].t,1 });
                                        best_pattern.push_back(ori_ma_bf_changed);
                                        best_pattern2.push_back({});
                                    }
                                }
                            }
                        }
                        if (t2 == 0 || ((s1!=t1||s2!=t2-1)&&S.Q[t1][t2 - 1] >= S.Q[s1][s2])) {
                            if (i - 1 != 0) {
                                temp.clear();
                                temp.reserve(i);
                                temp.push_back(x[i]);
                                for (int k = 0; k < i; ++k) {
                                    temp.push_back(x[k]);
                                }
                                int t3 = x[0].x;
                                int t4 = x[0].t;
                                if (t2 == 0 || S.Q[t1][t2 - 1] >= S.Q[t3][t4]) {
                                    R_temp.assign(i - 0 + 1, 0);
                                    Q_temp.assign(i - 0 + 1, 0);
									ori_ma_af_changed = ori_ma_bf_changed;
                                    ori_ma_af_changed.erase(ori_ma_af_changed.begin() + S.ope_on_machine[t1][t2].t);
                                    ori_ma_af_changed.insert(ori_ma_af_changed.begin()+ S.ope_on_machine[s1][s2].t, { t1,t2 });
                                    if (t2 == 0 && S.ope_on_machine[t3][t4].t == 0) {
                                        R_temp[0] = 0;
                                    }
                                    else {
                                        if (t2 == 0) {
                                            int s8 = S.ope_on_machine[t3][t4].t;
                                            int t5 = S.machine_ass[machine_num][s8-1].x;
                                            int t6 = S.machine_ass[machine_num][s8 - 1].t;
                                            R_temp[0] = S.R[t5][t6] + job[t5][t6][S.where_machine[t5][t6]].t;
                                        }
                                        else {
                                            if (S.ope_on_machine[t3][t4].t == 0) {
                                                R_temp[0] = S.R[t1][t2 - 1] + job[t1][t2 - 1][S.where_machine[t1][t2 - 1]].t;
                                            }
                                            else {
                                                int s8 = S.ope_on_machine[t3][t4].t;
                                                int t5 = S.machine_ass[machine_num][s8-1].x;
                                                int t6 = S.machine_ass[machine_num][s8 - 1].t;
                                                R_temp[0] = max(S.R[t5][t6] + job[t5][t6][S.where_machine[t5][t6]].t,
                                                    S.R[t1][t2 - 1] + job[t1][t2 - 1][S.where_machine[t1][t2 - 1]].t);
                                            }
                                        }
                                    }
                                    R_temp[1] = t4 == 0 ? R_temp[0] + job[t1][t2][S.where_machine[t1][t2]].t :
                                        max(S.Q[t3][t4 - 1] + job[t3][t4 - 1][S.where_machine[t3][t4 - 1]].t,
                                            R_temp[0] + job[t1][t2][S.where_machine[t1][t2]].t);
                                    for (int k = 0 + 1; k < i; ++k) {
                                        int t5 = x[k].x;
                                        int t6 = x[k].t;
                                        int t7 = x[k - 1].x;
                                        int t8 = x[k - 1].t;
                                        R_temp[k + 1] = t6 == 0 ? R_temp[k] + job[t7][t8][S.where_machine[t7][t8]].t :
                                            max(S.R[t5][t6 - 1] + job[t5][t6-1][S.where_machine[t5][t6 - 1]].t,
                                                R_temp[k] + job[t7][t8][S.where_machine[t7][t8]].t);
                                    }
                                    t3 = x[i - 1].x;
                                    t4 = x[i - 1].t;
                                    if (t4 == job[t3].size() - 1 && S.ope_on_machine[t1][t2].t == S.ope_count_per_machine[machine_num] - 1) {
                                        Q_temp[i - 0] = 0;
                                    }
                                    else {
                                        if (t4 == job[t3].size() - 1) {
                                            int s8 = S.ope_on_machine[t1][t2].t;
                                            int t5 = S.machine_ass[machine_num][s8+1].x;
                                            int t6 = S.machine_ass[machine_num][s8 + 1].t;
                                            Q_temp[i - 0] = S.Q[t5][t6] + job[t5][t6][S.where_machine[t5][t6]].t;
                                        }
                                        else {
                                            if(S.ope_on_machine[t1][t2].t == S.ope_count_per_machine[machine_num] - 1)
                                                Q_temp[i - 0] = S.Q[t3][t4 + 1] + job[t3][t4 + 1][S.where_machine[t3][t4]].t;
                                            else {
                                                int s8 = S.ope_on_machine[t1][t2].t;
                                                int t5 = S.machine_ass[machine_num][s8 + 1].x;
                                                int t6 = S.machine_ass[machine_num][s8 + 1].t;
                                                Q_temp[i - 0] = max(S.Q[t5][t6] + job[t5][t6][S.where_machine[t5][t6]].t,
                                                    S.Q[t3][t4 + 1] + job[t3][t4 + 1][S.where_machine[t3][t4+1]].t);
                                            }
                                        }
                                    }
                                    for (int k = i - 2; k > 0; --k) {
                                        int t5 = x[k].x, t6 = x[k].t;
                                        int t7 = x[k + 1].x, t8 = x[k + 1].t;
                                        Q_temp[k - 0 + 1] = t6 == job[t5].size() - 1 ? Q_temp[k - 0 + 2] + job[t7][t8][S.where_machine[t7][t8]].t :
                                            max(S.Q[t5][t6 + 1] + job[t5][t6 + 1][S.where_machine[t5][t6 + 1]].t,
                                                Q_temp[k - 0 + 2] + job[t7][t8][S.where_machine[t7][t8]].t);
                                    }
                                    Q_temp[0] = t2 == job[t1].size() - 1 ? Q_temp[1] + job[x[0].x][x[0].t][S.where_machine[x[0].x][x[0].t]].t:
                                        max(S.Q[t1][t2 + 1] + job[t1][t2+1][S.where_machine[t1][t2 + 1]].t,
                                            Q_temp[1] + job[x[0].x][x[0].t][S.where_machine[x[0].x][x[0].t]].t);
                                    int temp_makespan = 0;
                                    for (int k = 0; k < i - 0 + 1; ++k) {
                                        int s = R_temp[k] + job[temp[k].x][temp[k].t][S.where_machine[temp[k].x][temp[k].t]].t + Q_temp[k];
                                        temp_makespan = s > temp_makespan ? s : temp_makespan;
                                    }
                                    if (temp_makespan < best_makespan_tabu) {
										best_makespan_tabu = temp_makespan;
                                        best_move_tabu = { { t1,t2,x[0].x,x[0].t,0 } };
                                        best_pattern_tabu = ori_ma_bf_changed;
                                    }
                                    if (temp_makespan < best_makespan&& Tabu_table[machine_num].find(ori_ma_af_changed) == Tabu_table[machine_num].end()) {
                                        if (temp_makespan == best_makespan) {
                                            best_move.push_back({ t1,t2,x[0].x,x[0].t,0 });
                                            best_pattern.push_back(ori_ma_bf_changed);
                                            best_pattern2.push_back({});
                                        }
                                        else {
                                            best_makespan = temp_makespan;
                                            best_move.clear();
                                            best_pattern.clear();
                                            best_pattern.clear();
                                            best_move.push_back({ t1,t2,x[0].x,x[0].t,0 });
                                            best_pattern.push_back(ori_ma_bf_changed);
                                            best_pattern2.push_back({});
                                        }
                                    }
                                }
                            }
                        }
                        Nk_nei(x, S, i, best_makespan, best_move, Tabu_table, best_pattern,best_pattern2,best_move_tabu,best_pattern_tabu,best_makespan_tabu);
                        continue;
                    }
                }
            }
            else {
                Nk_nei(x, S, 0, best_makespan, best_move, Tabu_table, best_pattern,best_pattern2,best_move_tabu,best_pattern_tabu,best_makespan_tabu);
            }
        }
        for (auto& x : Tabu_table) {
            for (auto it = x.begin(); it != x.end();) {
                --(*it).second;
                if ((*it).second <= 0) {
                    it=x.erase(it);
                }
                else {
                    ++it;
                }
            }
        }
        vector<int> choosed_move;
        vector<cho> choosed_pattern;
        vector<cho> choosed_pattern2;
        if (best_move.size() > 0) {
            uniform_int_distribution<> dis1(0, best_move.size() - 1);
            int choose = dis1(gen);
            choosed_move = best_move[choose];
            choosed_pattern = best_pattern[choose];
            choosed_pattern2 = best_pattern2[choose];
        }
        else {
            choosed_move = best_move_tabu;
            choosed_pattern = best_pattern_tabu;
        }
        vector<int>  b(5, -1);
		vector<cho> tabu1, tabu2;
        int m_num = 0,m_num1=0;
        if (choosed_move != b) {
            m_num = S.ope_on_machine[choosed_move[0]][choosed_move[1]].x;
            if (choosed_move[2] != -2) {
                m_num1 = S.ope_on_machine[choosed_move[2]][choosed_move[3]].x;
            }
            else {
                m_num1 = choosed_move[3];
            }
        }
		int new_tabu_tenure = S.machine_ass[m_num].size() > 2 ? (S.machine_ass[m_num].size() - 2) * 3+1 : 5;
        if (choosed_pattern.size() != 0) {
            Tabu_table[m_num][choosed_pattern] = max(Tabu_tenure,new_tabu_tenure);
            if(choosed_pattern2.size()!=0)
                Tabu_table[m_num1][choosed_pattern2] = Tabu_tenure;
        }
        if (choosed_move != b) {
            make_move(choosed_move, S);
        }
        if (S.makespan < obj_best) {
            obj_best = S.makespan;
            cur = S;
            iter = 0;
        }
		if (obj_best < global_best_obj) {
			global_best_obj = obj_best;
			record_time.stop();
			record_time.start();
		}
        ++iter;
    }
    return;
}

Solution MAE(int p,Solution &S_star) {
    Solution S1, S2, Sc, Sp;
    Solution empty;
    Solution S_best;
    int iter = 0;
    Initial(S1);
    Initial(S2);
    Initial(Sc);
    caculate_makespan(Sc);
    Initial(Sp);
    caculate_makespan(Sp);
    caculate_makespan(S_star);
    Solution S1_temp;
    Solution S2_temp;
    int gen = 0;
    int best_obj = INT_MAX;
    double mae_time = 0;
    while (mae_time<=run_time) {
        stop_watch s;
        s.start();
        PR(S1, S2, S1_temp,0.4,0.6,5);
        PR(S2, S1, S2_temp,0.4,0.6,5);
        TS(S1_temp,S1);
        TS(S2_temp,S2);
        int t1, t2, t3;
        t1 = S1.makespan;
        t2 = S2.makespan;
        t3 = Sc.makespan;
        Sc = (t1<t2?t1:t2) < t3 ?(t1<t2?S1:S2): Sc;
        t3 = (t1 < t2 ? t1 : t2) < t3 ? (t1 < t2 ? t1 : t2) : t3;
        t1 = S_star.makespan;
        S_star = t1 < t3 ? S_star : Sc;
        if (S_star.makespan < best_obj) {
            best_obj = S_star.makespan;
            S_best=S_star;
            gen = 0;
        }
        ++gen;
		caculate_d(S1, S2);
        if (same_pos_count>= 0.8*ope_sum) {//需修改
            S2 = empty;
            Initial(S2);
            caculate_makespan(S2);
        }
        if (iter == p) {
            S1 = Sp;
            Sp = Sc;
            Sc = empty;
            Initial(Sc);
            caculate_makespan(Sc);
            iter = 0;
        }
        ++iter;
        s.stop();
        mae_time += s.elapsed_second();
    }
    return S_best;
}

int get_ope_time(int x,int t,int m) {
    for(int i=0;i<job[x][t].size();i++){
        if (job[x][t][i].x==m){
            return job[x][t][i].t;
        }
    }
    return 0;
}

vector<vector<cho>> caculate_ans(Solution &S) {
    vector<vector<cho>> ans=S.ope_on_machine;//二者结构相同
    vector<vector<int>> start_time(job_count);
    vector<int> now;//机器的now
    now.resize(machine_count,0);
    machine.resize(machine_count);
    for (int i = 0; i < job_count;++i) {
        start_time[i].resize(job[i].size(), 0);
    }
    for (int i=1;i<machine_count;i++){//机器号
        for (int j=0;j<S.machine_ass[i].size();j++){//工序在机器中的位置
            int tmp_x=S.machine_ass[i][j].x;//订单号
            int tmp_t=S.machine_ass[i][j].t;//工序在订单中的位置
            if(tmp_t>0){
                int tmp_now=start_time[tmp_x][tmp_t-1]+get_ope_time(tmp_x,tmp_t-1,S.ope_on_machine[tmp_x][tmp_t-1].x);
                now[i]=now[i]>tmp_now?now[i]:tmp_now;
            }
            start_time[tmp_x][tmp_t]=now[i];
            now[i]+=get_ope_time(tmp_x,tmp_t,S.ope_on_machine[tmp_x][tmp_t].x);
            machine[i].push_back({start_time[tmp_x][tmp_t],get_ope_time(tmp_x,tmp_t,S.ope_on_machine[tmp_x][tmp_t].x)});
        }
    }
    for (int i = 0; i < job_count; ++i) {
        for (int j = 0; j < job[i].size(); ++j) {
            ans[i][j].t=start_time[i][j];
        }
    }
    //print_machine(machine);
    return ans;
}

vector<vector<cho>> fjsp(int job_count,int machine_count,vector<vector<vector<cho>>> job){
    for (const auto& x : job) {
        ope_sum += x.size();
    }
    empty_QorR.resize(job_count);
	for (int i = 0; i < job_count; ++i)
		empty_QorR[i].resize(job[i].size(), -1);
    Solution test_s;
    Solution test_s1;
    Solution test_s2;
    Solution S_ans;
    Initial(test_s);
    Initial(test_s1);
    Initial(test_s2);
    caculate_makespan(test_s);
    record_time.start();
    S_ans=MAE(5,test_s1);
    return caculate_ans(S_ans);
}

vector<cho> insert(vector<vector<cho>> pans,int job_count,int machine_count,vector<vector<vector<cho>>> job,int itime){
    int earliest=itime+1;//当前工序最早开始时间
    vector<cho> additional_ans;
    for (int i=0;i<job[job_count-1].size();i++){
        int tmp_x=job[job_count-1][i][0].x;
        int tmp_t=job[job_count-1][i][0].t;
        for (int j=0;j<machine[tmp_x].size();j++){
            if(j==machine[tmp_x].size()-1){//插入到该机器的最后
                    int tmp_start=machine[tmp_x][j].x+machine[tmp_x][j].t>earliest?machine[tmp_x][j].x+machine[tmp_x][j].t:earliest;
                    machine[tmp_x].push_back({tmp_start,tmp_t});
                    additional_ans.push_back({tmp_x,machine[tmp_x][j+1].x});
                    earliest=machine[tmp_x][j+1].x+machine[tmp_x][j+1].t;
                    break;
                }
            else if(machine[tmp_x][j].x+machine[tmp_x][j].t>=earliest){//插入到该机器的j工序之后
                if(machine[tmp_x][j].x+machine[tmp_x][j].t+tmp_t<=machine[tmp_x][j+1].x){
                    machine[tmp_x].insert(machine[tmp_x].begin()+j+1,{machine[tmp_x][j].x+machine[tmp_x][j].t,tmp_t});
                    additional_ans.push_back({tmp_x,machine[tmp_x][j+1].x});
                    earliest=machine[tmp_x][j+1].x+machine[tmp_x][j+1].t;
                    break;
                }
            }
        }
    }
    return additional_ans;
}
