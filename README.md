# Dynamic-FJSP
Code for solving the Flexible job shop problem with 插单 operation.

相比教学网上的源代码,此代码做了一些微小变动:
将存储订单信息的vector由c[N]与C[N]改为了job与Job(实质上仍然是三维vector),对读取文件的代码也做出了相应修改
弃用固定的N,使用随着插单进行而增大的job_count
solve与resolve两个函数删去了没有用到的参数
未改变随机产生插单时间的功能
未改变检查ans是否合法的功能

运行时间主要由solver.h中的run_time决定,预设为150秒,实际可能会有数秒误差
误差主要来源于使用贪心的插单及由算法返回的Solution求ans的过程

Written for 算法设计与分析@PKU 2021-2022 2nd sem.
