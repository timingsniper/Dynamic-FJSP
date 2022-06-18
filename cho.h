#ifndef CHO_H
#define CHO_H
struct cho{
	int x,t;
	bool operator <(const cho &k)const{
		return t<k.t;
	}
	bool operator !=(const cho &k)const{
		return (t!=k.t)||(x!=k.x);
	}
};
#endif
