#ifndef SOL_H
#define SOL_H

#include"cho.h"
#include"solver.h"

#include<iostream>

vector<vector<cho>> solve(int n,int m,vector<vector<vector<cho>>> c){
	vector<vector<cho>> ans;
	ans.clear();
	ans=fjsp(n,m,job);
	return ans;
}
vector<vector<cho>> resolve(vector<vector<cho>>pans,int n,int m,vector<vector<vector<cho>>> c,int itime){
	vector<vector<cho>> ans=pans;
	ans.push_back(insert(pans,n,m,job,itime));
	return ans;
}
#endif
