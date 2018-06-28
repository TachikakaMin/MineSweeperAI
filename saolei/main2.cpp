#include <iostream>
#include <cstdlib>
#include <cstdio>
#include <algorithm>
#include <cstring>
#include <vector>
#include <ctime>
#include <random>
#include <queue>
#include <set>
#include <omp.h>
#include <map>
#include <iterator>
using namespace std;
const int NOT_SCAN = -2;
const int MINE = -1;
int dx[]={0, 0,1,-1,  1,-1,-1, 1};  //前四个是上下左右
int dy[]={1,-1,0, 0,  1,-1, 1,-1};
const int MAXN = 500;

template<class ForwardIt, class T, class Compare=std::less<> >
ForwardIt binary_find(ForwardIt first, ForwardIt last, const T& value, Compare comp={})
{
   	first = std::lower_bound(first, last, value, comp);
    return first != last && !comp(value, *first) ? first : last;
}

int mp[MAXN][MAXN],n,m; //mp 看见的局面
int ans[MAXN][MAXN]; //testcase的答案
int sure1[MAXN][MAXN]; //sure1 推测一定是雷的地方
int sure0[MAXN][MAXN]; //sure0 推测一定不是雷的地方
int is_Constrain[MAXN][MAXN]={0};//判断以这个点为中心的constrain是否加入
int mine_Num;
double p_mp[MAXN][MAXN]; //是雷的概率
namespace CSPRandomMinesweeper{
	const int TOT_RANDOM_NUM = 10000000;
	struct Constrain
	{	
		vector<pair<int,int> > p; //等式左边元素,x,y坐标
		int v; //等式右边
	};
	vector<Constrain> all_Constrain;
	vector<set<pair<int,int> > > v_set;
	vector<vector<int> > v_num;
	vector<int> type_Constrain;
	map<pair<int,int>,int> pro_mp;
	long long get_Pro_tot;
	int have_found=0;
	long long get_Pro_legal;
	void span(const int &x,const int &y) //开出0的情况
	{
		queue<int> q;
		q.push(x);q.push(y);
		while (!q.empty())
		{
			int ox = q.front();q.pop();
			int oy = q.front();q.pop();
			sure0[ox][oy]=1;
			int nx,ny;
			for (int i=0;i<4;i++)
			{
				nx = ox+dx[i];ny=oy+dy[i];
				if (mp[nx][ny]==NOT_SCAN && ans[nx][ny]==0)
				{
					mp[nx][ny]=0;
					q.push(nx);q.push(ny);
				}
				if (mp[nx][ny]==NOT_SCAN && ans[nx][ny]>0 && ans[nx][ny]<9)
				{
					mp[nx][ny] = ans[nx][ny];
				}
			}
		}
	}


	void update() //把新的constrain加入到序列中
	{
		for (int i=1;i<=n;i++)
			for (int j=1;j<=m;j++)
				if (mp[i][j]!=NOT_SCAN)
					if (!is_Constrain[i][j])
					{
						is_Constrain[i][j]=1;
						Constrain new_Constrain;
						for (int k=0;k<8;k++)
							new_Constrain.p.push_back(make_pair(i+dx[k],j+dy[k]));
						new_Constrain.v = mp[i][j];
						all_Constrain.push_back(new_Constrain);
						Constrain new_Constrain2;
						new_Constrain2.v = 0;
						new_Constrain2.p.push_back(make_pair(i,j));
						all_Constrain.push_back(new_Constrain2);
					}
	}

	void set_bound() //设置边界上的constrain
	{
		for (int i=0;i<=n+1;i++)
		{
			Constrain test;
			test.v = 0;
			test.p.push_back(make_pair(i,0));
			all_Constrain.push_back(test);
		}
		for (int i=1;i<=m+1;i++)
		{
			Constrain test;
			test.v = 0;
			test.p.push_back(make_pair(0,i));
			all_Constrain.push_back(test);
		}
		for (int i=1;i<=n+1;i++)
		{
			Constrain test;
			test.v = 0;
			test.p.push_back(make_pair(i,m+1));
			all_Constrain.push_back(test);
		}
		for (int i=1;i<=m;i++)
		{
			Constrain test;
			test.v = 0;
			test.p.push_back(make_pair(n+1,i));
			all_Constrain.push_back(test);
		}
	}

	void init()  //读入答案和初始化地图
	{
		// scanf("%d %d %d",&n,&m,&mine_Num);
		for (int i=0;i<=n+1;i++)
			for (int j=0;j<=m+1;j++)
			{
				mp[i][j]=sure1[i][j]=sure0[i][j]=is_Constrain[i][j]=0;
				p_mp[i][j]=0;
				all_Constrain.clear();
				v_set.clear();
				v_num.clear();
				type_Constrain.clear();
				pro_mp.clear();
				have_found=0;
				get_Pro_tot=0;
				get_Pro_legal=0;
			}
		// for (int i=1;i<=n;i++)
		// 	for (int j=1;j<=m;j++)
		// 		scanf("%d",&ans[i][j]);
		for (int i=1;i<=n;i++)
			for (int j=1;j<=m;j++)
				mp[i][j]=NOT_SCAN;
		set_bound();
	}

	void debug_Print() //打印局面信息
	{
		for (int i=1;i<=n;i++)
		{
			for (int j=1;j<=m;j++)
				if (mp[i][j]<0) cout << "\u25A0 ";
					else printf("%d ",mp[i][j]);
			printf("\n");
		}
	}

	bool can_Reduce(int x,int y)  //判断两个constrain是否能相消
	{
		Constrain a = all_Constrain[x];
		Constrain b = all_Constrain[y];
		if (a.p.size()==b.p.size()) return 0;
		bool switch_ab = 0;
		if (a.p.size()>b.p.size()) swap(a,b),switch_ab = 1;
		sort(a.p.begin(), a.p.end());
		sort(b.p.begin(), b.p.end());
		Constrain ans;
		ans.v = b.v - a.v;
		int cnt=0;
		int i=0;
		while (i<b.p.size()&&cnt<a.p.size())
			if (b.p[i]!=a.p[cnt])
				ans.p.push_back(b.p[i]),i++;
			else i++,cnt++;
		while (i<b.p.size())
			ans.p.push_back(b.p[i]),i++;
		if (ans.p.size()!=b.p.size()-a.p.size()) return 0;
		if (!switch_ab) all_Constrain[y] = ans;
			else all_Constrain[x] = ans;
		return 1;
	}

	void if_All_Mine(int i) //碰到 x+y+z=3 变成 x=1 y=1 z=1
	{
		for (int j = 1;j<all_Constrain[i].p.size();j++)
		{
			Constrain test;
			test.v = 1;
			test.p.push_back(all_Constrain[i].p[j]);
			all_Constrain.push_back(test);
		}
		Constrain test;
		test.v = 1;
		test.p.push_back(all_Constrain[i].p[0]);
		all_Constrain[i] = test;
	}

	void if_All_Not_Mine(int i) //碰到 x+y+z=0 变成 x=0 y=0 z=0
	{
		for (int j = 1;j<all_Constrain[i].p.size();j++)
		{
			Constrain test;
			test.v = 0;
			test.p.push_back(all_Constrain[i].p[j]);
			all_Constrain.push_back(test);
		}
		Constrain test;
		test.v = 0;
		test.p.push_back(all_Constrain[i].p[0]);
		all_Constrain[i] = test;
	}

	bool divide() // 分解x+y+z=3 x+y+z=0
	{
		int len = all_Constrain.size();
		bool b=0;
		for (int i=0;i<len;i++)
		{
			if (all_Constrain[i].p.size()==all_Constrain[i].v && all_Constrain[i].v>1)
				if_All_Mine(i),b=1;
			if (all_Constrain[i].v == 0 && all_Constrain[i].p.size()>1)
				if_All_Not_Mine(i),b=1;
		}
		return b;
	}

	void sure()//把确定的点加入sure0 sure1
	{
		int len = all_Constrain.size();
		for (int i=0;i<len;i++)
			if (all_Constrain[i].p.size()==1)
			{
				int x,y;
				x = all_Constrain[i].p[0].first;
				y = all_Constrain[i].p[0].second;
				if (all_Constrain[i].v == 0)
					sure0[x][y]=1;
				else sure1[x][y]=1;
			}
		for (int i=1;i<=n;i++)
			for (int j=1;j<=m;j++)
				if (mp[i][j]!=MINE && mp[i][j]!=NOT_SCAN) sure0[i][j]=1;
	}
	void debug_P_MP_Print()
	{
		printf("\n");
		for (int i=1;i<=n;i++)
		{
			for (int j=1;j<=m;j++)
				printf("%.3lf  ",p_mp[i][j]);
			printf("\n");
		}
	}
	void check_Constrain() //检查是否有constrain能推断的
	{
		int len;
		while (1)
		{
			len = all_Constrain.size();
			bool b=0;
			for (int i=0;i<len;i++)
				for (int j=i+1;j<len;j++)
					if (can_Reduce(i,j)) b=1;
			if (divide()) b=1;
			if (b==0) break;
		}
		sure();
	}

	void print_Constrain() //打印constrain信息
	{
		for (int i=0;i<all_Constrain.size();i++)
		{
			printf("%d\n",i);
			for (int j=0;j<all_Constrain[i].p.size();j++)
				printf("(%d,%d) ",all_Constrain[i].p[j].first,all_Constrain[i].p[j].second);
			printf("%d\n",all_Constrain[i].v);
		}
	}

	bool check_Certain()  //检查是否有确定不是雷的
	{
		for (int i=1;i<=n;i++)
			for (int j=1;j<=m;j++)
				if (mp[i][j]==NOT_SCAN && sure0[i][j]==1)
					return 1;
		return 0;
	}

	int logic_choose() //根据逻辑推断选择
	{
		for (int i=1;i<=n;i++)
			for (int j=1;j<=m;j++)
				if (mp[i][j]==NOT_SCAN && sure0[i][j]==1)
				{
					mp[i][j]=ans[i][j];
					//printf("logic choose (%d, %d)\n",i,j);
					// if (ans[i][j]==MINE) 
					// {
					// 	printf("1\n");
					// 	return
					// }
					if (ans[i][j]==0) span(i,j);
					return 1;
				}
		return 0;
	}

	bool guess_choose() //根据概率模型选择
	{
		int x,y; 
		double d=1;
		int tot=0;
		for (int i=1;i<=n;i++)
			for (int j=1;j<=m;j++)
				if (mp[i][j]==NOT_SCAN) tot++;
		for (int i=1;i<=n;i++)
			for (int j=1;j<=m;j++)
				if (mp[i][j]==NOT_SCAN)
				{
					if (p_mp[i][j]<d) 
					{
						d = p_mp[i][j];
						x = i;y=j;
						tot = 1;
					}
					if (p_mp[i][j]==d)
					{
						tot++;
						bool b = rand()%tot;
						if (b==0) {d = p_mp[i][j];x=i;y=j;}
					}
				}
		mp[x][y]=ans[x][y];
		// printf("guess choose (%d, %d)\n",x,y);
		if (mp[x][y]==MINE) 
		{
			// debug_P_MP_Print();
			//printf("guess choose (%d, %d)\n",x,y);
			// printf("0\n");
			return 0;
		}
		if (mp[x][y]==0) span(x,y);
		return 1;
	}

	bool choose() //选择下一步选那个点,并根据答案判断选的点是不是雷
	{
		if (logic_choose()) {update();return 1;}
		if (guess_choose()) {update();return 1;} //如果没死，就把新的信息加进去
		return 0;
	}


	void initial_P_MP() //每一轮概率模型初始化
	{
		int num_mine=0;
		int num_not_scan=0;
		for (int i=1;i<=n;i++)
			for (int j=1;j<=m;j++) p_mp[i][j]=1;
		for (int i=1;i<=n;i++)
			for (int j=1;j<=m;j++)
				if (mp[i][j]!=NOT_SCAN && mp[i][j]!=MINE && mp[i][j]!=0)
				{
					int x = 0;
					for (int k=0;k<8;k++) 
						if (j+dy[k]>0 && j+dy[k]<=m && i+dx[k]>0 && i+dx[k]<n && mp[i+dx[k]][j+dy[k]]==NOT_SCAN) x++;
					for (int k=0;k<8;k++)
						p_mp[i+dx[k]][j+dy[k]] = min(p_mp[i+dx[k]][j+dy[k]],(double)mp[i][j]/x);
				}
		for (int i=1;i<=n;i++)
			for (int j=1;j<=m;j++)
			{
				if (sure0[i][j]) p_mp[i][j]=0;
				if (sure1[i][j]) p_mp[i][j]=1,num_mine++;
				if (mp[i][j]==NOT_SCAN) num_not_scan++;
			}
		double p=(double)(mine_Num-num_mine)/num_not_scan;
		for (int i=1;i<=n;i++)
			for (int j=1;j<=m;j++)
				if (!sure0[i][j]&&!sure1[i][j]&&mp[i][j]==NOT_SCAN)
					p_mp[i][j]=p;
	}

	bool check_Game_Is_End() //判断是否成功结束,不判断死亡
	{
		bool b=1;
		for (int i=1;i<=n;i++)
			for (int j=1;j<=m;j++)
				if (mp[i][j]==NOT_SCAN && ans[i][j]!=MINE)
					b=0;
		if (b)
		{
			// printf("1\n");
			return 1;
		}
		return 0;
	}
// ---------------------------------------------------------------------
// 
// 
// 
// 

	bool is_Connect(int x,int y) //判断两个constrain是否有公共元素
	{
		Constrain a = all_Constrain[x];
		Constrain b = all_Constrain[y];
		for (int i=0;i<a.p.size();i++)
			for (int j=0;j<b.p.size();j++)
				if (a.p[i]==b.p[j]) return 1;
		return 0;
	}

	int find_Fa(int x) //并查集
	{
		if (type_Constrain[x]!=x) type_Constrain[x]=find_Fa(type_Constrain[x]);
		return type_Constrain[x];
	}

	void conbine_Constrain(int a,int b) //合并并查集
	{
		int x = find_Fa(a),y=find_Fa(b);
		type_Constrain[x]=y;
	}

	void debug_type_Constrain()
	{
		int len = all_Constrain.size();
		for (int i=0;i<len;i++)
			if (type_Constrain[i]!=i)
				printf("%d %d\n",i,type_Constrain[i]);
		printf("\n");
	}

	void combine_Group() //将有所有公共元素的constrain的并查集合并
	{
		int len = all_Constrain.size();
		type_Constrain.clear();
		for (int i=0;i<len;i++) //并查集初始化
			type_Constrain.push_back(i);
		for (int i=0;i<len;i++)
			for (int j=i+1;j<len;j++)
				if (all_Constrain[i].p.size()!=1 && all_Constrain[j].p.size()!=1)
					if (is_Connect(i,j)) conbine_Constrain(i,j);
	}


	void find_Mine_Group() //对每个group sample他们雷的可能数
	{
		int len = all_Constrain.size();
		for (int i=0;i<len;i++) find_Fa(i);
		v_set.clear();v_num.clear();
		for (int i=0;i<len;i++) 
		{
			set<pair<int,int> > s;
			v_set.push_back(s);
			std::vector<int> v;
			v_num.push_back(v);
		}
		for (int i=0;i<len;i++)
		{
			if (all_Constrain[i].p.size()==1) continue;
			if (type_Constrain[i]!=i) continue;
			for (int j=0;j<len;j++)
				if (type_Constrain[j]==i) 
				{
					for (int k=0;k<all_Constrain[j].p.size();k++)
					{
						v_set[i].insert(all_Constrain[j].p[k]);
						v_num[i].push_back(j);
					}
				}
		}
	}


	void debug_v_set()
	{
		printf("debug_v_set ---------------\n");
		for (int i=0;i<v_set.size();i++)
			if (v_set[i].size()>1) printf("%d %lu\n",i,v_set[i].size());
		printf("\n"); 
	}


	bool check_mp(int id)
	{
		int len = v_num[id].size();		
		for (int i=0;i<len;i++)
		{
			int o = v_num[id][i];
			int x=0;
			for (int k=0;k<all_Constrain[i].p.size();k++)
				x+=pro_mp[all_Constrain[i].p[k]];
			if (x!=all_Constrain[i].v) return 0;
		}
		return 1;
	}

	void get_Pro(const int &id_num,const vector<pair<int,int> > &v)
	{
		have_found=0;
		for (int i=1;i<=n;i++)
			for (int j=1;j<=m;j++) if (sure1[i][j]) have_found++;
		get_Pro_legal = 1;
		get_Pro_tot = (long long)1<<(long long)min((int)v.size(),17);
		vector<long long> cnt1;
		for (int j=0;j<v.size();j++) cnt1.push_back(0);
		if (v.size()>17)
		{
			for (long long i=0;i<get_Pro_tot;i++)
			{
				pro_mp.clear();
				int tot1=0;
				for (int j=0;j<v.size();j++)
				{
					pro_mp[v[j]] = rand()%2;
					tot1+=pro_mp[v[j]];
				}
				if (tot1<=mine_Num-have_found && check_mp(id_num))
				{
					get_Pro_legal++;
					for (int j=0;j<v.size();j++)
						cnt1[j]+=pro_mp[v[j]];
				}
				// printf("\r%lld/%lld",i,get_Pro_tot);
	   //      	fflush(stdout);
			}
			for (int i=0;i<v.size();i++)
			{
				int x=v[i].first;
				int y=v[i].second;
				p_mp[x][y] = (double)cnt1[i]/get_Pro_legal;
			}
			return ;
		}
		for (long long i=0;i<get_Pro_tot;i++)
		{
			pro_mp.clear();
			long long x = i;
			int tot1=0;
			for (int j=0;j<v.size();j++)
			{
				pro_mp[v[j]] = x%2;
				tot1+=pro_mp[v[j]];
				x/=2;
			}
			if (tot1<=mine_Num-have_found && check_mp(id_num))
			{
				get_Pro_legal++;
				for (int j=0;j<v.size();j++)
					cnt1[j]+=pro_mp[v[j]];
			}
			// printf("\r%lld/%lld",i,get_Pro_tot);
   //      	fflush(stdout);
		}
		for (int i=0;i<v.size();i++)
		{
			int x=v[i].first;
			int y=v[i].second;
			p_mp[x][y] =min(p_mp[x][y],(double)cnt1[i]/get_Pro_legal);
		}
	}

	void sample()
	{
		int len = v_set.size();
		for (int i=0;i<len;i++)
			if (v_set[i].size()>1 && v_set[i].size()<60)
			{
				vector<pair<int,int> > sample_item;
				for (auto it = v_set[i].cbegin();it!=v_set[i].cend();it++)
					sample_item.push_back(*it);
			 	get_Pro(i,sample_item);
			}
	}

	int main1()
	{
		init();
		while (1)
		{
			// printf("---------------------\n");
			// print_Constrain();
			// debug_Print();
			if (check_Game_Is_End()==1) return 0;
			check_Constrain(); //逻辑推断
			if (check_Certain())
			{
				if (choose()==0) return 1;
				update();
				continue;
			}
			combine_Group();
			find_Mine_Group();
			// debug_type_Constrain();
			// debug_v_set();
			initial_P_MP();
			sample();
			// debug_P_MP_Print();
			// 
			if (choose()==0) return 1; //选择新点
		}
		return 0;
	}
}


namespace RandomData{
	vector<int> q;
	int main1()
	{
		n=30,m=16;
		mine_Num = 99;
		for (int i=0;i<=n+1;i++)
			for (int j=0;j<=m+1;j++) ans[i][j]=0;
		q.clear();
		int cnt=0;
		while (cnt<mine_Num)
		{
			int x=rand()%n+1;
			int y=rand()%m+1;
			bool b = 0;
			for (int i=0;i<q.size();i+=2) 
				if (q[i]==x&&q[i+1]==y) {b=1;break;}
			if (b==0) {q.push_back(x);q.push_back(y);cnt++;}
		}
		for (int i=0;i<q.size();i+=2) 
		{
			int x = q[i],y=q[i+1];
			ans[x][y]=-1;
			for (int j=0;j<8;j++)
				if (ans[x+dx[j]][y+dy[j]]!=-1)
					ans[x+dx[j]][y+dy[j]]++;
		}
		// printf("%d %d %d\n",n,m,mine_Num);
		// for (int i=1;i<=n;i++)
		// {
		// 	for (int j=1;j<=m;j++)
		// 		printf("%d ",ans[i][j]);
		// 	printf("\n");
		// }
		return 0;
	}
}

int main(int argc, char const *argv[])
{
	int cnt1=0,t_o_t=1000;
	srand((unsigned int)time(NULL));
	// #pragma omp parallel for reduction(+:cnt1)
	for (int i=1;i<=t_o_t;i++)
	{
		// freopen("t_e_s_t.in","w",stdout);
		RandomData::main1();
		// freopen ("/dev/tty", "a", stdout);
		// printf("2333\n");
		// freopen("t_e_s_t.in","r",stdin);
		if (CSPRandomMinesweeper::main1()==0) cnt1++;
			// else cnt1=0;
		// freopen ("/dev/tty", "a", stdin);
	}
	printf("%lf\n",(double)cnt1/t_o_t);
	return 0;
}

