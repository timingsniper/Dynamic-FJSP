//相比教学网上的源代码,此代码做了一些微小变动
//将存储订单信息的vector由c[N]与C[N]改为了job与Job（实质上仍然是三维vector）,对读取文件的代码也做出了相应修改
//弃用固定的N,使用随着插单进行而增大的job_count
//solve与resolve两个函数删去了没有用到的参数
//未改变随机产生插单时间的功能
//未改变检查ans是否合法的功能

//运行时间主要由solver.h中的run_time决定,预设为150秒,实际可能会有数秒误差
//误差主要来源于使用贪心的插单与由算法返回的Solution求ans的过程

#include"sol.h"
#include"solver.h"

#include<vector>
#include<cstdio>
#include<cstdlib>
#include<algorithm>

#define seed 0
/*#define N 40*/
#define M 20
#define K 10

using namespace std;

int result[10];
void errorexit(char * c){printf("%s",c);exit(0);}
inline int get_result(vector<vector<cho>> ans,vector<vector<vector<cho>>> c,int n,int m){
	int ret=0;
	vector<cho> procedure_on_machine[M];
	for(int i=1;i<=m;i++)procedure_on_machine[i].clear();
	for(int i=0;i<n;i++){
		if(c[i].size()!=ans[i].size())
			errorexit("Error: invaild procedure number");
		int now=0;
		for(int j=0;j<c[i].size();j++){
			bool flag=1;
			if(ans[i][j].t<now)
				errorexit("Error: invaild start time");
			for(int k=0;(k<c[i][j].size())&&flag;k++)
				if(ans[i][j].x==c[i][j][k].x){
					flag=0;
					now=ans[i][j].t+c[i][j][k].t;
					procedure_on_machine[ans[i][j].x].push_back((cho){c[i][j][k].t,ans[i][j].t});
				}
			if(flag)
				errorexit("Error: invaild machine number");
		}
		ret=max(ret,now);
	}
	for(int i=1;i<=m;i++){
		sort(procedure_on_machine[i].begin(),procedure_on_machine[i].end());
		int now=0;
		for(int j=0;j<procedure_on_machine[i].size();j++){
			if(now>procedure_on_machine[i][j].t)
				errorexit("Error: invaild machine use");
			now=procedure_on_machine[i][j].x+procedure_on_machine[i][j].t;
		}
	}
	return ret;
}
void check_new_sol(vector<vector<cho>> newans,vector<vector<cho>> ans,int itime,int n){
	for(int i=0;i<n;i++){
		int now=0;
		for(int j=0;j<job[i].size();j++){
			bool flag=1;
			for(int k=0;(k<job[i][j].size())&&flag;k++)
				if(ans[i][j].x==job[i][j][k].x){
					flag=0;
					if((ans[i][j].t<=itime)&&(newans[i][j]!=ans[i][j]))
						errorexit("Error: invaild new answer");
					now=ans[i][j].t+job[i][j][k].t;
				}
		}
	}
}
int notime[K];
int main(int argc,char* argv[]){
	srand(seed);
	freopen(argv[1],"r",stdin);
	scanf("%d%d%d",&job_count,&machine_count,&insert_count);
	machine_count+=1;
	job_count-=insert_count;
	job.resize(job_count);
	int upperbound=0;
	for(int i=0;i<job_count;i++){
		int num;
		scanf("%d",&num);
		job[i].resize(num);
		int sumt=0;
		for(int j=0;j<num;j++){
			int num2;
			scanf("%d",&num2);
			for(int k=0;k<num2;k++){
				cho tmp;
				scanf("%d%d",&tmp.x,&tmp.t);
				job[i][j].push_back(tmp);
			}
			sort(job[i][j].begin(),job[i][j].end());
			sumt+=job[i][j][0].t;
		}
		upperbound=max(upperbound,sumt);
	}
	Job=job;
	for(int i=0;i<insert_count;i++)
		notime[i]=rand()%upperbound;
	sort(notime,notime+insert_count);
	ans=solve(job_count,machine_count,job);
	result[0]=get_result(ans,Job,job_count,machine_count);
	//print_ans(ans);
	
	/*for(int i=job_count;i<job_count+insert_count;i++){
		int num;
		scanf("%d",&num);
		for(int j=0;j<num;j++){
			int num2;
			vector<cho> tmpv;
			tmpv.clear();
			scanf("%d",&num2);
			for(int k=0;k<num2;k++){
				cho tmp;
				scanf("%d%d",&tmp.x,&tmp.t);
				tmpv.push_back(tmp);
			}
			job[i].push_back(tmpv);
			Job[i].push_back(tmpv);
		}
		int itime=notime[i-job_count];
		tmpans=resolve(ans,i+1,machine_count,job_count+insert_count-i-1,job,itime);
		if(tmpans[i][0].t<=itime)
			errorexit("Error: invaild new order start time");
		//result[i-job_count+1]=get_result(tmpans,Job,i+1,machine_count);
		check_new_sol(tmpans,ans,itime,i);
		ans=tmpans;
	}*/

	for(int i=0;i<insert_count;i++){
        job_count+=1;
        job.resize(job_count);
        Job.resize(job_count);
        global_best_obj=INT_MAX;
        ope_sum=0;
        int num;
        scanf("%d",&num);
        job[job_count-1].resize(num);
        for(int j=0;j<num;j++){
			int num2;
			scanf("%d",&num2);
            job[job_count-1][j].reserve(num2);
			for(int k=0;k<num2;k++){
                cho tmp;
				scanf("%d%d",&tmp.x,&tmp.t);
                job[job_count-1][j].push_back(tmp);
			}
			sort(job[job_count-1][j].begin(),job[job_count-1][j].end());
		}
        Job[job_count-1]=job[job_count-1];
        int itime=notime[i];
        tmpans=resolve(ans,job_count,machine_count,job,itime);
        if(tmpans[job_count-1][0].t<=itime)
			errorexit("Error: invaild new order start time");
		result[i+1]=get_result(tmpans,Job,job_count,machine_count);
		check_new_sol(tmpans,ans,itime,i);
		ans=tmpans;
		//print_ans(ans);
    }
	printf("Succeed,your result is below.\n");
	for(int i=0;i<=insert_count;i++)printf("%d\n",result[i]);
}
