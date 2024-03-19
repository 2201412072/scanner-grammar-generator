#include<iostream>
#include<fstream>
#include<queue> 
#include<cstring>
#include<map>
#include<set>
#include<bitset>


#include<windows.h>


using namespace std;
/*
//该程序生成LR系列分析器 
目前的语法：
1、#terminal id int id int ……；
2、#nonterminal id  ……；
3、id：id1 id2 ……
	|……； 
4、#left id id  ……;其实没啥用，默认都是左结合 
5、#right id id ……;
6、#priority id int id int ……;
7、#result string; 
其中3中如果想要非终结符为单个字符，可以用/后跟单个字符，不用添加在
nonterminal上，程序内部自动将它添加到map中
其中7中string只能取LR0，LR1，SLR和LALR中之一。 
默认起始文法为第一条文法

目前打算该程序通过LL文法生成，文法如下：
S->id: {add(id,point)} C;
	|#terminal A;|#nonterminal B|#left D;|#right E;
	|#priority F;|#result string {result=string} ;
A->id int {map_terminal[id]=int} A|epsilon
B->id {map_nonterminal[id]=-find_int()} B|epsilon
C->id C|single C| '|'C|epsilon
其中single是词法分析器识别出来的单个字符，说明见程序语法说明部分  
D->id D|epsilon
E->id E|epsilon
F->id int F|epsilon


注意事项：
1、 在写产生式时，表示文法结尾的$符最开始在map中存的值为
	10086，所以不要将terminal赋值成10086，但是后来在计算
	cal_first前会将其修改成一个正常的、没使用过的值 
2、程序会默认输出的第一个产生式左部为初始非终结符，然后会
	添加一条新产生式， S__begin —> S $end，所以不要将终结
	符、非终结符命名成 $end和S__begin
	（S__begin在map_nonternimal中为-1，同时该产生式在栈中的前三个单位，即0，1，2） 
3、 用#terminal时数字最好从1开始
4、 该程序在识别字符时不太对劲，所有不包括；的string均可被
	识别，所以在写程序时应小心，确保随时空格。
5、在词法分析时，23号优先级最低。 

 
！！！！用#terminal时所用的id必须为[a-zA-Z0-9]*，其他无法识别，这是一个大bug，完了必须重新修改词法分析器 

我目前感觉词法分析不用23，而实际上程序里面也没有用23 



a_first等用于记录一个非终结符的所有产生式开始的位置；a_con等用于记录
一个非终结符在first时所能更新的所有非终结符；a等记录一个非终结符在stack中
的位置 
*/
/*
目前进度：
1、构建文法图 
2、求first集  ……//求了 
3、求follow集  ……//求了 
4、构建lr项目集 ……//求了 
5、构建lr1项目集

输出时我打算全输出正数，即为search_minus和终结符，这样生成的程序速度会快一些 

一开始lr0是1，然后通过dfa来读入终结符，再通过edge来转移，然后通过reduce来
判断是否归约，如果归约，通过back来出相应个数的栈，通过reduce来归约入栈 


6、化简项目集（lalr）
7、变成自动机语言
目前想法有两条：1、自己实现lr项目集，这样容易转变各种项目集，
				2、转化为自动机来实现， 但是这个会产生许多状态，同时各个项目集不太好转化 


8、follow集处理边（slr）
9、处理优先级和结合性
目前研究发现： 优先级和结合性可以通过断dfa的边来实现，同时dfa中提供的优先级
根本没用，无法与语法制导方案相容。 

10、判断是否有冲突 


目前我有两个栈，一个是stack，它记录了每个产生式；还有一个是stack_approach
，它在stack对应位置不为0时记录了stack此时产生式左侧的非终结符；
如stack对应位置为0，则它记录了下一个产生式的最后一个符号的位置 

目前我打算再写一个txt，将详细信息都写进去，这样，程序就不用管报错后
提供原项目集的信息啥的了，就只用报哪个项目集编号有问题就行了 

目前我准备将ans_back和ans_reduce删除，将信息全部存在ans_edge中 

*/
FILE *fp;
char *output_pro,*output_array,*output_detail;
char *file_name;
int state,now;//state代表当前状态
struct dfa_result_node{
	int result,indicator;
}DFA__s;
queue<dfa_result_node> dfa_result;//dfa_result代表目前识别出来的结果
int dfa_array[20][128];
int count_dfa;//count_dfa代表dfa的状态个数
int dfa_to[20],dfa_from;//dfa_to代表某个状态是否为接受状态，以及如是应输出什么
struct node {
	int num;
	string content;
};
string show_non[1000];
string show_ter[1000];//两个都只是用来输出的 
int number_lr0;//lr0项目集的个数，从0开始 
int maxx_num;//它用于记录terminal和转成正数后的nonterminal的最大值是多少，
//方便以后建邻接矩阵时确定它的大小 
int temp_show;
int cnt;
int point,cnt_first,flag_token,cnt_nonterminal;
int a[100],last[100],location[100];
int a_first[100],last_first[100],location_first[100];
int flag_first=0;//1表示已经有一个产生式了，不用考虑￥了，否则在第一个产生式后要加￥ 
int flag_ter_c=0;//1表示产生式中已经有终结符，后面的非终结符不用再add_con了，反正也不会更新；0代表没有 
int cnt_con=0,a_con[100],last_con[100],y_con[100];
int fa[1000],isright[100],priority[100]={0}; 
int nonidC;//nonidC是S->id:C中的id的值
int stack[1000];//文法栈，隔离符是0，正数是终结符，负数是非终结符 
int stack_approach[1000]; 
string strA,strB,strC,strD,strF,result,record_str;
map<string,int> map_terminal,map_nonterminal;
map<int,int> map_epsilon; //map_epsilon存储stack上哪些位子上有epsilon，并记录它属于哪条产生式 
//map_terminal存储正数,nonterminal存储负数 
node nowken;
bitset<100> first_set[100];
bitset<100> temp_first;//用于记录在执行某条产生式时，其计算得出的first集 

bitset<100> follow_set[100];
bitset<100> temp_follow; 

map<set<int> ,int > map_lr0; 
int search_nonterminal[1000];//记录了nonterminal变成正数后，正数对应的负数 
int search_minus[1000];//记录了nonterminal变成正数后，负数对应的正数


int ans_edge[1000][1000];//邻接矩阵，该输出的结果
//转换表如为正表示移进，负表示归约，其中前11位(第一位是符号位)表示归约的长度，后面的表示要归约成的项目集 
int ans_reduce[1000];//记录某一项目集是否该归约,如不该为-1，否则为要规约的非终结符（正数）（map_nonterminal中的值，不过取绝对值） 
int ans_back[1000];//记录归约时需要退的长度 
int record_PDA_end;//记录pda结束状态 

ofstream code_out; 

void cal_stack_approach();
void cal_first();
void cal_follow();
void change_minus();
void cal_SLR();
void write_array();
void write_detail();
void  write_code();
int load_edge(int length,int destination)
{
	int ans=0;
	ans=length<<20;
	ans+=destination;
	ans=-ans;
	return ans;
}
void write_name(char* ch,string str,int l)
{
	strcpy(ch,file_name);
	int i;
	for(i=0;i<str.length();i++,l++)
	{
		ch[l]=str[i];
	}
	ch[l+1]='\0';
}
int dfa_init()
{
	int i,j;
	ifstream mycin("自动机程序_LR_array.txt");
	mycin>>count_dfa;
	for(i=0;i<count_dfa;i++)
	{
		for(j=0;j<128;j++)
		{
			mycin>>dfa_array[i][j];
		}
	}
	mycin>>dfa_from;
	for(i=0;i<count_dfa;i++)
	{
		mycin>>dfa_to[i];
	}
}
void dfa_state(string &str)
{
	DFA__s.indicator=-1;
	DFA__s.result=-1;
	now=0;
	record_str="";
	int l=str.size();
	state=dfa_from;
	while(now<l)
	{
		if(dfa_to[state]!=-1)
		{
			DFA__s.indicator=now;
			DFA__s.result=dfa_to[state];
		}
		if(dfa_array[state][str[now]]==-1)
		{
			record_str=str.substr(now);
			//return ;
			break;
		}
		state=dfa_array[state][str[now]];
		now++;
	}
	if(dfa_to[state]!=-1)
	{
		DFA__s.result=dfa_to[state];
		DFA__s.indicator=now;
	}
}
node get_token()
{
	string str;
	if(record_str=="")
	{
		cin>>str;
		dfa_state(str);
	}
	else
	{
		str=record_str;
		dfa_state(str);
	}
	node ans_get;
	if(DFA__s.result==-1)
	{
		//error();//读入无法被词法分析器识别 
		ans_get.num=0;
		ans_get.content="";
	}
	else
	{
		ans_get.num=DFA__s.result;
		ans_get.content=str.substr(0,DFA__s.indicator);
	}
	return ans_get;
}
node now_token()
{
	if(!flag_token)
	{
		flag_token=1;
		nowken=get_token();
		if(nowken.num==3)
		{
			if(nowken.content=="epsilon")
			{
				nowken.num=22;
			}
			
		}
		if(nowken.num==1)
		{
			if(nowken.content=="#nonterminal")
			{
				nowken.num=2;
			}
			else if(nowken.content=="#left")
			{
				nowken.num=18;
			}
			else if(nowken.content=="#right")
			{
				nowken.num=19;
			}
			else if(nowken.content=="#priority")
			{
				nowken.num=20;
			}
			else if(nowken.content=="#result")
			{
				nowken.num=21;
			}
			else if(nowken.content=="#terminal")
			{
				//nowken.num=1;
			}
			else
			{
				//error();
			}
		}
		//cout<<nowken.num<<" "<<nowken.content<<endl;
	}
	
	//cout<<nowken.num<<" "<<nowken.content<<endl;
	return nowken;
}
void add(int x)//add用于记录一个非终结符在文法栈中的所有位置 
{
	cnt++;
	last[cnt]=a[x];
	location[cnt]=point;
	a[x]=cnt;
}
void add_first(int x)//add_first用于记录一个非终结符E的所有产生式的开头在文法栈中的位置 
{
	cnt_first++;
	last_first[cnt_first]=a_first[x];
	location_first[cnt_first]=point;
	a_first[x]=cnt_first;
}
void add_con(int x,int y)
//add_con表示一个非终结符E在产生式右侧，可以通过它更新的左侧非终结符的集合
//（意思是如果它在终结符右边就不在该集合中） 
{
	cnt_con++;
	last_con[cnt_con]=a_con[x];
	y_con[cnt_con]=y;
	a_con[x]=cnt_con;
}
int find(int x)//并查集查找第一个没有使用的terminal元素 ,fa记录了第一个不使用的 
{
	if(fa[x]==x) return x;
	fa[x]=find(fa[x]);
	return fa[x];
}
int strtoint(string str)
{
	int len=str.size();
	int ans=0;
	for(int i=0;i<len;i++)
	{
		ans*=10;
		ans+=(str[i]-'0');
	}
	return ans;
}
void deal_A()
{
	node temp=now_token();
	if(temp.num==3||temp.num==5||temp.num==23)
	{
		flag_token=0;
		if(temp.num==5) strA=temp.content.substr(1,1);
		else strA=temp.content;
		temp=now_token();
		if(temp.num==4)
		{
			if(map_nonterminal.count(strA))
			{
				//error();
			}
			else if(map_terminal.count(strA))
			{
				//error();
			}
			else
			{
				int temp_int;
				temp_int=strtoint(temp.content);
				maxx_num=temp_int>maxx_num? temp_int:maxx_num;
				map_terminal[strA]=temp_int;
				temp_int=find(temp_int);
				fa[temp_int]=find(temp_int+1);
			}
			
		}
		else
		{
			//error();
		}
		flag_token=0;
		deal_A();
	}
	else if(temp.num==6)
	{
		return ;
	}
	else
	{
		//error();
	}
}
void deal_B()
{
	node temp=now_token();
	if(temp.num==3)
	{
		if(map_terminal.count(temp.content))
		{
			//error();
		}
		else if(map_nonterminal.count(temp.content))
		{
			//error();
		}
		else
		{
			cnt_nonterminal--;
			map_nonterminal[temp.content]=cnt_nonterminal;
		}
		flag_token=0;
		deal_B();
	}
	
	else if(temp.num==6)
	{
		return ;
	}
	else
	{
		//error();
	}
}
void deal_C()
{
	node temp=now_token();
	if(temp.num==3||temp.num==23)//23好像没有，它已经被T就给排了 
	{
		if(map_terminal.count(temp.content))
		{
			stack[point]=map_terminal[temp.content];
			stack_approach[point]=nonidC;
			point++;
			flag_ter_c=1;
		}
		else if(map_nonterminal.count(temp.content))
		{
			if(!flag_ter_c&&map_nonterminal[temp.content]!=nonidC)
			{
				add_con(-map_nonterminal[temp.content],nonidC);
			}
			stack[point]=map_nonterminal[temp.content];
			stack_approach[point]=nonidC;
			add(-stack[point]);
			point++;
		}
		else
		{
			//error();
		}
		flag_token=0;
		deal_C();
	}
	else if(temp.num==5)//处理single 
	{
		string str=temp.content.substr(1,1);
		if(map_terminal.count(str))
		{
			stack[point]=map_terminal[str];
			stack_approach[point]=nonidC;
			point++;
			
		}
		else
		{
			int temp_C=find(1);
			map_terminal[str]=temp_C;
			stack[point]=temp_C;
			stack_approach[point]=nonidC;
			point++;
			maxx_num=maxx_num>temp_C?maxx_num:temp_C;
			fa[temp_C]=find(temp_C+1);
		}
		flag_ter_c=1;
		flag_token=0;
		deal_C();
	}
	else if(temp.num==7)//处理"|" 
	{
		stack[point]=0;
		point++;
		add_first(nonidC);
		flag_token=0;
		deal_C();
	}
	else if(temp.num==22)//处理如果输入为epsilon保留字的情况 
	{
		map_epsilon[point]=nonidC;
		flag_token=0;
		deal_C();
	}
	else if(temp.num==6)//处理";" 
	{
		stack[point]=0;
		point++;
		return ;
	}
	else
	{
		//error();
		return ;
	}
}
void deal_D()
{
	node temp=now_token();
	if(temp.num==3)
	{
		flag_token=0;
		deal_D();
	}
	else if(temp.num==6)
	{
		return ;
	}
	else
	{
		//error();
	}
}
void deal_E()
{
	node temp=now_token();
	if(temp.num==3)
	{
		flag_token=0;
		if(!map_terminal.count(temp.content))
		{
			//error();
		}
		else
		isright[map_terminal[temp.content]]=1;
		deal_E();
	}
	else if(temp.num==6)
	{
		return ;
	}
	else
	{
		//error();
		return ;
	}
}
void deal_F()
{
	node temp=now_token();
	if(temp.num==3)
	{
		flag_token=0;
		strF=temp.content;
		if(!map_terminal.count(strF))
		{
			//error();
			strF="";
		}
		temp=now_token();
		flag_token=0;
		if(temp.num==4)
		{
			priority[map_terminal[strF]]=strtoint(temp.content);
		}
		else
		{
			//error();
			
		}
		deal_F();
	}
	else if(temp.num==6)
	{
		return ;
	}
	else
	{
		//error();
	}
}
void deal_S()
{
	node temp=now_token();
	if(temp.num==1)
	{
		flag_token=0;
		deal_A();
	}
	else if(temp.num==2)
	{
		flag_token=0;
		deal_B();
	}
	else if(temp.num==18)
	{
		flag_token=0;
		deal_D();
	}
	else if(temp.num==19)
	{
		flag_token=0;
		deal_E();
	}
	else if(temp.num==20)
	{
		flag_token=0;
		deal_F();
	}
	else if(temp.num==21)
	{
		flag_token=0;
		temp=now_token();
		if(temp.content!="LR1"&&temp.content!="SLR"&&temp.content!="LALR"&&temp.content!="LR0")
		{
			//error();
		}
		flag_token=0;
		result=temp.content;
	}
	else if(temp.num==3)
	{
		flag_ter_c=0;//1表示产生式中已经有终结符，后面的非终结符不用再add_con了，反正也不会更新；0代表没有 
		if(!map_nonterminal.count(temp.content))
		{
			//error();
		}
		//add(temp.content);
		nonidC=-map_nonterminal[temp.content];//nonidC是S->id:C中的id的值,map_nonterminal中存的是负值 
		if(!flag_first)
		{
			map_nonterminal["S__begin"]=-1;
			add_first(1);
			add_con(nonidC,1);
			stack[point]=-nonidC;//用户第一条产生式
			stack_approach[point]=1;
			add(nonidC);
			point++;
			stack[point]=10086;//$
			stack_approach[point]=1;
			point++;
			stack[point]=0;
			point++;
			flag_first=1;
		}
		add_first(nonidC);
		//strC=temp.content;
		flag_token=0;
		temp=now_token();
		if(temp.num==8)
		{
			flag_token=0;
			deal_C();
		}
		else 
		{
			//error();
			flag_token=0;
		}
	}
	else 
	{
		//error();
		flag_token=0;
	}
	temp=now_token();
	if(temp.num==6)
	{
		flag_token=0;
		return ;
	}
	else 
	{
		//error();
		flag_token=0;
	}
}
void deal_T()
{
	node temp=now_token();
	if(temp.num&&(temp.num<=3||(temp.num>=18&&temp.num<=22)))
	{
		deal_S();
		deal_T();
	}
	else if(!temp.num)
	{
		return ;
	}
	else
	{
		//error();
	}
}
int main()
{
	int i;
	dfa_init();
	file_name="cfg_LR.txt";
	int len=strlen(file_name);
	//output
	output_detail=new char[len+8];
	write_name(output_detail,"_detail.txt",len-4);
	cnt=0;
	point=0,cnt_first=0,flag_token=0,cnt_nonterminal=-1;
	string mean_group[23];
	for(i=1;i<1000;i++)
	{
		fa[i]=i;
		ans_reduce[i]=-1;
	}
	mean_group[1]="#terminal",mean_group[3]="id",mean_group[4]="int";
	mean_group[5]="/[a-zA-Z]",mean_group[6]=";",mean_group[7]="|";
	mean_group[2]="#nonterminal",mean_group[22]="epsilon",mean_group[18]="#left";
	mean_group[19]="#right",mean_group[20]="#priority",mean_group[21]="#result";
	freopen(file_name,"r",stdin);
	state=dfa_from;
	map_terminal["$end"]=10086;//10086是为了方便辨认，完了要修改 
	deal_T();
	//以下是修改￥的值，不要让它是10086 
	i=find(1);
	fa[i]=find(i+1);
	map_terminal["$end"]=i;
	stack[1]=i;
	
	map<string,int>::iterator iter;
	//输出非终结符以及它在程序中存的值 
	cout<<"nonterminal:"<<endl; 
	for(iter=map_nonterminal.begin();iter!=map_nonterminal.end();iter++)
	{
		cout<<(*iter).first<<" "<<(*iter).second<<endl;
		show_non[-(*iter).second]=(*iter).first;
	}
	//输出终结符以及它在程序中存的值 
	cout<<"\nterminal:"<<endl;
	cout<<"epsilon 0"<<endl;
	for(iter=map_terminal.begin();iter!=map_terminal.end();iter++)
	{
		cout<<(*iter).first<<" "<<(*iter).second<<endl;
		show_ter[(*iter).second]=(*iter).first;
	} 
	cal_stack_approach();
	change_minus();//！！！！！！未检验
	cout<<"stack_number:"<<endl;
	for(i=0;i<=point;i++)
	{
		cout<<stack[i]<<" ";
	}
	cout<<endl;
	cout<<"stack:"<<endl;
	for(i=0;i<=point;i++)
	{
		//cout<<stack[i]<<" ";
		if(stack[i]>0)
		{
			cout<<show_ter[stack[i]]<<" ";
		}
		else if(stack[i]<0)
		{
			cout<<show_non[-stack[i]]<<" ";
		}
		else cout<<0<<" ";
	}
	cout<<endl;
	cout<<"stack_approach:"<<endl;
	for(i=0;i<=point;i++)
	{
		cout<<stack_approach[i]<<" ";
	}
	cout<<endl;  
	
	if(result=="SLR")
	{
		cal_first();
		cal_follow();
		cal_SLR();
		output_pro=new char[len+15];
		output_array=new char[len+11];
		write_name(output_pro,"_slr_procedure.txt",len-4);
		write_name(output_array,"_slr_array.txt",len-4);
		write_array();
	}
	else
	{
		if(result=="LR0")
		{
			cal_SLR();
			output_pro=new char[len+15];
			output_array=new char[len+11];
			write_name(output_pro,"_lr0_procedure.txt",len-4);
			write_name(output_array,"_lr0_array.txt",len-4);
			write_array();
		}
	}
	/*for(i=1;i<=-cnt_nonterminal;i++)
	{
		cout<<"first["<<map_nonterminal[i]<<"]:"<<first_set[i]<<endl;
	}*/
	//map<string,int>::iterator iter;
	
	//输出first集 
	for(iter=map_nonterminal.begin();iter!=map_nonterminal.end();iter++)
	{
		temp_show=-(*iter).second;
		cout<<"first["<<(*iter).first<<"]: ";
		for(int j=0;j<100;j++)
		{
			if(first_set[temp_show][j])
			{
				cout<<j<<" ";
			}
		}
		cout<<endl;
		//cout<<"first["<<(*iter).first<<" "<<(*iter).second<<"]="<<first_set[-(*iter).second]<<endl;
	 }
	//输出follow集 
	cout<<"\n";
	for(iter=map_nonterminal.begin();iter!=map_nonterminal.end();iter++)
	{
		temp_show=-(*iter).second;
		cout<<"follow["<<(*iter).first<<"]: ";
		for(int j=0;j<100;j++)
		{
			if(follow_set[temp_show][j])
			{
				cout<<j<<" ";
			} 
		}
		cout<<endl;
	 }
	 map<int,int>::iterator ite;
	 cout<<"\n";
	 cout<<"map_epsilon:\n";
	 for(ite=map_epsilon.begin();ite!=map_epsilon.end();ite++)
	 {
	 	cout<<(*ite).first<<" "<<(*ite).second<<endl;
	 } 
	 //输出lr0项目集
	 cout<<"\n";
	 cout<<"LR0:\n";
	 SetConsoleOutputCP(437);
	 map<set<int> ,int>::iterator it;
	 for(it=map_lr0.begin();it!=map_lr0.end();it++)
	 {
	 	set<int> temp_s=(*it).first;
	 	cout<<(*it).second<<":\n";
	 	set<int>::iterator setiter;
	 	int k,temp_k;
	 	char temp_c=254;
	 	for(setiter=temp_s.begin();setiter!=temp_s.end();setiter++)
	 	{
	 		//cout<<(*setiter)<<" ";
	 		k=*setiter;
			if(stack[*setiter]==0)
			{
				temp_k=k-1;
			}
			else temp_k=k;
			for(;stack[temp_k];temp_k--){}
			temp_k++;
			if(stack[temp_k]) 
			cout<<show_non[stack_approach[temp_k]]<<":";
			else cout<<" :";//epsilon，我也不知道咋处理，就以空格代替 
			for(;temp_k<k;temp_k++)
			{
				//cout<<stack[temp_k]<<" ";
				if(stack[temp_k]>0)
					cout<<show_ter[stack[temp_k]]<<" ";
				else cout<<show_non[-stack[temp_k]]<<" ";
			}
			cout<<temp_c;
			for(;stack[temp_k];temp_k++)
			{
				if(stack[temp_k]>0)
					cout<<show_ter[stack[temp_k]]<<" ";
				else cout<<show_non[-stack[temp_k]]<<" ";
			}
			cout<<"    ";
		}
		cout<<endl;
	}
	cout<<"\n";
	cout<<"num:\n";
	for(i=1;i<=maxx_num;i++)
	{
		cout<<i<<":";
		if(search_nonterminal[i])
			cout<<search_nonterminal[i]<<" ";
		else cout<<i<<" ";
	}
	cout<<"\n";
	cout<<"edge:\n";
	int show_temp=1<<20;
	show_temp--;
	for(i=1;i<=number_lr0;i++)
	{
		cout<<i<<":\n";
		for(int j=1;j<=maxx_num;j++)
		{
			if(!ans_edge[i][j])  continue;
			if(search_nonterminal[j])
			{
				cout<<show_non[-search_nonterminal[j]]<<":";
			}
			else
				cout<<show_ter[j]<<":";	
			if(ans_edge[i][j]>0)
			{		
				cout<<ans_edge[i][j]<<" ";	
			}
			else if(ans_edge[i][j]<0)
			{
				int temp=(-ans_edge[i][j])&show_temp;
				cout<<"reduce"<<temp<<" ";
			}
			
		}
		cout<<"\n";
	} 
	cout<<"\n";
	cout<<"\n";
	cout<<"ans_reduce:\n";
	for(i=1;i<=number_lr0;i++)
	{
		if(ans_reduce[i]>0)
		{
			cout<<show_non[ans_reduce[i]]<<" ";
		}
		else cout<<ans_reduce[i]<<" ";	
	}
	cout<<"\n";
	cout<<"ans_back:\n";
	for(i=1;i<=number_lr0;i++)
	{
		cout<<ans_back[i]<<"  ";	
	} 
	write_detail(); 
	write_code();
}
void cal_first()//在rebuild以前实现的，所以用的旧图 
{
	int judge[1000],temp_non;
	queue<int> q;//队列里只有first暂时还没有epsilon的非终结符 
	for(int i=0;i<1000;i++)
	{
		judge[i]=0;
	}
	map<string,int>::iterator iter;
	for(iter=map_nonterminal.begin();iter!=map_nonterminal.end();iter++)
	{
		temp_non=-(*iter).second;
		q.push(temp_non);
		judge[temp_non]=1;
	}
	while(!q.empty())//仅考虑epsilon 
	{
		int top=q.front();
		q.pop();
		judge[top]=0;
		if(first_set[top][0]) continue;
		for(int k=a_first[top];k;k=last_first[k])//查看它所有的产生式 
		{
			int now_stack=stack[location_first[k]]; 
			if(now_stack==0)//如果可以产生epsilon 
			{
				first_set[top][0]=1;//标记 
				for(int j=a_con[top];j;j=last_con[j])//找到所有它可能更新的非终结符 
				{
					if(!judge[y_con[j]]&&!first_set[y_con[j]][0])
					//如果它没在队列里面,而且它不产生epsilon 
					{
						judge[y_con[j]]=1;
						q.push(y_con[j]);//加入队列 
					}
				}
				break;
			}
			else if(now_stack<0)
			{
				int temp=first_set[-now_stack][0];
				if(!temp) continue;
				int place=location_first[k]+1;
				while(stack[place]<0&&temp)
				{
					temp&=first_set[-stack[place]][0];
					place++;
				}
				if(stack[place]<=0&&temp)
				{
					first_set[top][0]=1; 
					for(int j=a_con[top];j;j=last_con[j])//找到所有它可能更新的非终结符 
					{
						if(!judge[y_con[j]]&&!first_set[y_con[j]][0])
						//如果它没在队列里面,而且它不产生epsilon 
						{
							judge[y_con[j]]=1;
							q.push(y_con[j]);//加入队列 
						}
					}
					break;
				}
			}
			else continue;
		}
	}
	//计算first集 
	for(iter=map_nonterminal.begin();iter!=map_nonterminal.end();iter++)
	{
		temp_non=-(*iter).second;
		if(!judge[temp_non])
		{
			q.push(temp_non);
			judge[temp_non]=1; 
		}
	}
	while(!q.empty())
	{	
		int top=q.front(),flag_first=0;//flag_first用于判断非终结符是否更新 
		q.pop();
		judge[top]=0;
		temp_first=first_set[top];
		for(int k=a_first[top];k;k=last_first[k])//查看它所有的产生式 
		{
			//temp_first=first_set[top];
			int now_stack=stack[location_first[k]];
			if(now_stack==0)
			{
				continue;
			}
			else if(now_stack>0)
			{
				if(!temp_first[now_stack])
				{
					temp_first[now_stack]=1;
					//flag_first=1;
				}
				continue;
			}
			else
			{
				temp_first|=first_set[-now_stack];
				//temp_first[0]=first_set[-now_stack][0];
				//if(!temp_first[0])
				if(!first_set[-now_stack][0]) 
				{
					//temp_first[0]=first_set[top][0];
					/*if(temp_first==first_set[top])
					{
						continue;
					}
					else
					{
						flag_first=1;
						first_set[top]=temp_first;
						continue;
					}*/
					continue;
				}
				int place=location_first[k]+1;
				while(stack[place]!=0)
				{
					if(stack[place]>0)
					{
						temp_first[stack[place]]=1;
						break;
					}
					else 
					{
						temp_first|=first_set[-stack[place]];
						//temp_first[0]=first_set[-stack[place]][0];
						if(!first_set[-stack[place]][0]) break;
						place++; 
					}
				}		
				/*temp_first[0]=first_set[top][0];
				if(temp_first==first_set[top])
				{
					continue;
				}
				else
				{
					first_set[top]=temp_first;
					flag_first=1;
					continue;
				}*/
			}
		}
		temp_first[0]=first_set[top][0];
		if(temp_first==first_set[top])
		{
			continue;
		}
		//else
		/*{
			first_set[top]=temp_first;
			flag_first=1;
			//continue;
		}*/
		first_set[top]=temp_first;
		//if(!flag_first) continue;
		for(int j=a_con[top];j;j=last_con[j])//找到所有它可能更新的非终结符 
		{
			if(!judge[y_con[j]]&&y_con[j]!=top)
			//如果它没在队列里面 
			{
				judge[y_con[j]]=1;
				q.push(y_con[j]);//加入队列 
			}
		}
	}
}
void cal_stack_approach()
{
	int k=0;
	for(int i=2;i<point;i++)
	{
		if(!stack[i]) 
		{
			if(k)
			stack_approach[k]=i-1;//stack_approach中对应的stack的0时，存下一个产生式多久结束,记下结束地址 
			k=i;
		}
	}
}
void cal_follow()
{
	//follow_set[-stack[0]][stack[1]]=1;
	int judge[1000],temp_non,now_stack,k=0;
	queue<int> q; 
	for(int i=0;i<1000;i++)
	{
		judge[i]=0;
	}
	
	map<string,int>::iterator iter;
	for(iter=map_nonterminal.begin();iter!=map_nonterminal.end();iter++)
	{
		temp_non=-(*iter).second;
		if(temp_non!=1)
			q.push(temp_non);
		judge[temp_non]=1;
	}
	while(!q.empty())
	{
		int top=q.front(),place;
		q.pop();
		judge[top]=0;
		temp_follow=follow_set[top];
		for(k=a[top];k;k=last[k])
		{ 
			place=location[k]+1;
			now_stack=stack[place];
			if(now_stack==0)
			{
				temp_follow|=follow_set[stack_approach[place-1]];
			}
			else if(now_stack>0)
			{
				temp_follow[now_stack]=1;
			}
			else 
			{
				while(now_stack<0)
				{
					temp_follow|=first_set[-now_stack];
					if(!first_set[-now_stack][0]) break;
					place++;
					now_stack=stack[place];
				}
				if(now_stack==0)
				{
					temp_follow|=follow_set[stack_approach[place-1]];
				}
				else if(now_stack>0)
				{
					temp_follow[now_stack]=1;
				}
			}
		}
		temp_follow[0]=0;
		if(temp_follow!=follow_set[top])
		{
			follow_set[top]=temp_follow;
			for(k=a[top];k;k=last[k])//它在产生式右边，则将它左边非终结符加入q 
			{
				place=location[k]-1;
				if(place<0) continue;
				now_stack=stack[place];
				if(!now_stack) continue;
				if(now_stack<0&&!judge[-now_stack]&&now_stack!=-top)
				{
					judge[-now_stack]=1;
					q.push(-now_stack);
				}
			}
			for(k=a_first[top];k;k=last_first[k])//它在产生式左边，则将它的所以产生式最后一个非终结符加入q 
			{
				place=location_first[k]-1;
				place=stack_approach[place];
				now_stack=stack[place];
				if(now_stack<0&&!judge[-now_stack]&&now_stack!=-top)
				{
					judge[-now_stack]=1;
					q.push(-now_stack);
				}
			}	
		}
	}
}
void change_minus()
{
	int i=-1,temp_change;
	for(;i>=cnt_nonterminal;i--)
	{
		temp_change=find(1);
		search_minus[-i]=temp_change;
		maxx_num=maxx_num>temp_change?maxx_num:temp_change;
		search_nonterminal[temp_change]=i;
		fa[temp_change]=find(temp_change+1);
	}
}
/*
void cal_edge_epsilon()//从stack何stack_approach中计算出如果有epsilon，该归约成什么
{
	int k,now_non,temp_location;
	map<string,int>::iterator iter;
	for(iter=map_nonterminal.begin();iter!=map_nonterminal.end();iter++)
	{
		now_non=-(*iter).second;
		if(now_non==1) continue;
		for(k=a_first[now_non];k;k=last_first[k])
		{
			temp_location=location_first[k];
			if(temp_location-1==stack[temp_location-1])
			{
				ans_edge[]
			}
		}
	 } 
} 
*/
void cal_SLR() //好像可以map里套set 
{
	int temp_q,k,top,element;
	int temp_end,temp_edge;//temp_edge用于记录一个项目集是否有边连出 
	//temp_end用于记录是否有产生式结束，以及有几个结束 
	bitset<1000> temp_record;//用于记录某一个产生式是否已经处理过 
	bitset<1000> record_element;//记录一个lr0项目集向其他项目集连边时，是否有多条产生式对应同一个元素 
	//number_lr0=1; 
	//queue<node_lr0_point> q_all;//记录项目集 
	queue<set<int> >q_all;//记录项目集 
	queue<int> q_build; // 记录一个项目集中所有的产生式
	set<int> s,s_top;
	q_build.push(0);
	s.insert(0);
	temp_end=0; 
	while(!q_build.empty())
	{
		temp_q=q_build.front();
		q_build.pop();
		if(stack[temp_q]<0)
		{
			k=a_first[-stack[temp_q]];
			for(;k;k=last_first[k])
			{
				if(temp_record[location_first[k]]) continue;
				s.insert(location_first[k]);
				q_build.push(location_first[k]);
				temp_record[location_first[k]]=1;
			}
		}
		else if(stack[temp_q]==0)
		{
			temp_end++;
		}	
	}
	/*if(!map_lr0.count(s))
	{
		
		number_lr0++;
		map_lr0[s]=number_lr0;
	}*/
	number_lr0=1;
	map_lr0[s]=1;
	//if(temp_end)
	q_all.push(s);
	while(!q_all.empty())
	{
		s_top=q_all.front();
		q_all.pop();
		record_element.reset(); 
		//temp_record.reset();
		temp_edge=0; 
		set<int>::iterator iter,it;
		for(iter=s_top.begin();iter!=s_top.end();iter++)
		{
			if(stack[*iter])
			{
				temp_record.reset();
				if(stack[*iter]<0)
				{
					element=search_minus[-stack[*iter]];
				}
				else element=stack[*iter];
				//以上为了计算出一个项目对应的正数 
				if(record_element[element]) continue;
				record_element[element]=1;
				//以上记录该项目 
				//temp_edge=0; 
				s.clear();
				//ans_edge[map_lr0[s_top]][element]=;
				s.insert((*iter)+1);
				q_build.push((*iter)+1);
				for(it=iter;it!=s_top.end();it++)
				{
					if(it==iter) continue;
					if(stack[*it]==stack[*iter])//查看上一项目集是否有相同的边连到待更新的这个项目集中 
					{
						q_build.push((*it)+1);
						s.insert((*it)+1);
					}
				}
				while(!q_build.empty())//处理该情况的项目拓展eg S->·E拓展E->·a 
				{
					top=q_build.front();
					temp_record[top]=1;
					q_build.pop();
					if(stack[top]<0)
					{
						for(k=a_first[-stack[top]];k;k=last_first[k])
						{
							if(!temp_record[location_first[k]])
							{
								q_build.push(location_first[k]);
								s.insert(location_first[k]);
								temp_record[location_first[k]]=1;
							}
						}
					}
				}
				if(!map_lr0.count(s))
				{
					number_lr0++;
					map_lr0[s]=number_lr0;
					ans_edge[map_lr0[s_top]][element]=number_lr0;
					q_all.push(s);
				}
				else
				{
					ans_edge[map_lr0[s_top]][element]=map_lr0[s];
				}
			}
			else
			{
				temp_edge++;//计算一个项目集中归约的个数，理论上应该为1
				if(temp_edge>2)
				{
					//error()
				 } 
				int temp_pro=map_lr0[s_top];//项目集
				int back_num=0,temp_i=*iter,temp_edge_num;
				if(temp_i==2)
				{
					record_PDA_end=temp_pro;
				}
				temp_i--;
				while(temp_i>=0&&stack[temp_i])//计算归约需要出栈的数量 
				{
					temp_i--;
					back_num++;
				}
				if(back_num)
				temp_edge_num=load_edge(back_num,search_minus[stack_approach[(*iter)-1]]);
				//stack_approach[(*iter)-1]表示该项目的左侧非终结符，但是如果书写不规范如S->E epsilon W，就无法得出正确结果
				else//处理epsilon 
				{
					temp_edge_num=load_edge(0,search_minus[map_epsilon[(*iter)]]); 
				 } 
				/*for(int i=1;i<=maxx_num;i++)
				{
					if(!ans_edge[temp_pro][element])
					ans_edge[temp_pro][element]=temp_edge_num;
				} */
				int temp_nonterminal;
				int temp_record;
				if(back_num)
					temp_nonterminal=stack_approach[(*iter)-1];
				else 
				{
					temp_nonterminal=map_epsilon[(*iter)];
				}
				map<string,int>::iterator non_iter;
				for(non_iter=map_terminal.begin();non_iter!=map_terminal.end();non_iter++)
				{
					temp_record=(*non_iter).second;
					if(follow_set[temp_nonterminal][temp_record])
					{
						if(ans_edge[temp_pro][temp_record]>0)
						{
							//error//移进归约冲突 
						}
						else if(ans_edge[temp_pro][temp_record]>0) 
						{
							//error//归约归约冲突 
						}
						else
						{
							ans_edge[temp_pro][temp_record]=temp_edge_num;
						} 
					}
				 } 
			}
		}
		if(temp_edge) 
		{
			//int count_back=0;
			//int rubbish_temp,rubbish_temp2;
			if(s_top.size()==1)
			{
				iter=s_top.begin();
				int rubbish_temp=map_lr0[s_top],rubbish_temp2=(*iter)-1; 
				ans_reduce[rubbish_temp]=stack_approach[rubbish_temp2];//记录非终结符 
				k=a_first[ans_reduce[rubbish_temp]];
				while(location_first[k]>rubbish_temp2)
					k=last_first[k];
				k=location_first[k];
				if(k) ans_back[rubbish_temp]=stack_approach[k-1]-k+1;
				else ans_back[rubbish_temp]=2;
			}
			else
			{
				//error归约归约冲突 
			 }
		}	
	}	
} 
void write_array()
{
	ofstream mycout;
	int i;
	mycout.open(output_array,ios::out|ios::trunc);
	/* 
	//输出栈（我也不知道为啥要输出） 
	mycout<<point<<endl;
	for(i=0;i<point;i++)
	{
		if(stack[i]<0) mycout<<search_minus[-stack[i]]<<" ";
		else mycout<<stack[i]<<" ";
	}
	mycout<<endl;
	*/
	//输出最后判断是否成功的标志：是否最后归约到了S__begin了，S__begin的数字就是search_minus[1] 
	mycout<<record_PDA_end;
	mycout<<endl;
	mycout<<map_terminal["$end"]<<endl;
	//number_lr0和maxx_num直接作为宏定义输出，这里不用输出了 
	//mycout<<number_lr0<<" "<<maxx_num<<endl;
	//输出lr0是否应该归约，如果应该，则输出非终结符
	//（map_nonterminal中的值，不过取绝对值） 
	/*for(i=1;i<=number_lr0;i++)
	{
		if(ans_reduce[i]>0) 
			mycout<<search_minus[ans_reduce[i]]<<" ";
		else mycout<<-1<<" ";
	}
	mycout<<endl;
	for(i=1;i<=number_lr0;i++)
	{
		mycout<<ans_back[i]<<" ";
	}
	mycout<<endl<<endl;*/
	for(i=1;i<=number_lr0;i++)
	{
		for(int j=0;j<=maxx_num;j++)//0为epsilon 
		{
			mycout<<ans_edge[i][j]<<" ";
		}
		mycout<<endl;
	}
}
void write_detail()//用于写详细信息，方便用户查找错误 
{
	int i;
	ofstream decout;
	decout.open(output_detail,ios::out|ios::trunc); 
	map<string,int>::iterator iter;
	//输出非终结符以及它在程序中存的值 
	decout<<"nonterminal:"<<endl; 
	for(iter=map_nonterminal.begin();iter!=map_nonterminal.end();iter++)
	{
		decout<<(*iter).first<<" "<<(*iter).second<<endl;
		show_non[-(*iter).second]=(*iter).first;
	}
	//输出终结符以及它在程序中存的值 
	decout<<"\nterminal:"<<endl;
	//cout<<"epsilon 0"<<endl;
	for(iter=map_terminal.begin();iter!=map_terminal.end();iter++)
	{
		decout<<(*iter).first<<" "<<(*iter).second<<endl;
		show_ter[(*iter).second]=(*iter).first;
	} 
	//输出非终结符、终结符在生成的程序中的值 
	decout<<"\n";
	decout<<"num:\n";
	for(i=1;i<=maxx_num;i++)
	{
		decout<<i<<":";
		if(search_nonterminal[i])
			decout<<search_nonterminal[i]<<" ";
		else decout<<i<<" ";
	}
	decout<<"stack:"<<endl;
	for(i=0;i<=point;i++)
	{
		decout<<stack[i]<<" ";
	}
	decout<<endl;
	decout<<"stack_approach:"<<endl;
	for(i=0;i<=point;i++)
	{
		decout<<stack_approach[i]<<" ";
	}
	decout<<endl;
	if(result=="SLR")
	{
		//输出first集 
		for(iter=map_nonterminal.begin();iter!=map_nonterminal.end();iter++)
		{
			temp_show=-(*iter).second;
			decout<<"first["<<(*iter).first<<"]: ";
			for(int j=0;j<100;j++)
			{
				if(first_set[temp_show][j])
				{
					decout<<j<<" ";
				}
			}
			decout<<endl;
			//cout<<"first["<<(*iter).first<<" "<<(*iter).second<<"]="<<first_set[-(*iter).second]<<endl;
		 }
		//输出follow集 
		decout<<"\n";
		for(iter=map_nonterminal.begin();iter!=map_nonterminal.end();iter++)
		{
			temp_show=-(*iter).second;
			decout<<"follow["<<(*iter).first<<"]: ";
			for(int j=0;j<100;j++)
			{
				if(follow_set[temp_show][j])
				{
					decout<<j<<" ";
				} 
			}
			decout<<endl;
		} 
		 //输出lr0项目集
		 decout<<"\n";
		 decout<<"LR0:\n";
		 //SetConsoleOutputCP(437);
		 map<set<int> ,int>::iterator it;
		 for(it=map_lr0.begin();it!=map_lr0.end();it++)
		 {
		 	set<int> temp_s=(*it).first;
		 	decout<<(*it).second<<":\n";
		 	set<int>::iterator setiter;
		 	int k,temp_k;
		 	
		 	char temp_c1=0xA1,temp_c2=0xF1;
		 	for(setiter=temp_s.begin();setiter!=temp_s.end();setiter++)
		 	{
		 		//cout<<(*setiter)<<" ";
		 		k=*setiter;
				if(stack[*setiter]==0)
				{
					temp_k=k-1;
				}
				else temp_k=k;
				for(;stack[temp_k];temp_k--){}
				temp_k++;
				decout<<show_non[stack_approach[temp_k]]<<":";
				for(;temp_k<k;temp_k++)
				{
					//cout<<stack[temp_k]<<" ";
					if(stack[temp_k]>0)
						decout<<show_ter[stack[temp_k]]<<" ";
					else decout<<show_non[-stack[temp_k]]<<" ";
				}
				decout<<temp_c1<<temp_c2;
				for(;stack[temp_k];temp_k++)
				{
					if(stack[temp_k]>0)
						decout<<show_ter[stack[temp_k]]<<" ";
					else decout<<show_non[-stack[temp_k]]<<" ";
				}
				decout<<"    ";
			}
			decout<<endl;
		}
	}
	else
	{
		if(result=="LR0")
		{
			//输出lr0项目集
			 decout<<"\n";
			 decout<<"LR0:\n";
			 //SetConsoleOutputCP(437);
			 map<set<int> ,int>::iterator it;
			 for(it=map_lr0.begin();it!=map_lr0.end();it++)
			 {
			 	set<int> temp_s=(*it).first;
			 	decout<<(*it).second<<":\n";
			 	set<int>::iterator setiter;
			 	int k,temp_k;
			 	char temp_c1=0xA1,temp_c2=0xF1;
			 	for(setiter=temp_s.begin();setiter!=temp_s.end();setiter++)
			 	{
			 		//cout<<(*setiter)<<" ";
			 		k=*setiter;
					if(stack[*setiter]==0)
					{
						temp_k=k-1;
					}
					else temp_k=k;
					for(;stack[temp_k];temp_k--){}
					temp_k++;
					decout<<show_non[stack_approach[temp_k]]<<":";
					for(;temp_k<k;temp_k++)
					{
						//cout<<stack[temp_k]<<" ";
						if(stack[temp_k]>0)
							decout<<show_ter[stack[temp_k]]<<" ";
						else decout<<show_non[-stack[temp_k]]<<" ";
					}
					decout<<temp_c1<<temp_c2;
					for(;stack[temp_k];temp_k++)
					{
						if(stack[temp_k]>0)
							decout<<show_ter[stack[temp_k]]<<" ";
						else decout<<show_non[-stack[temp_k]]<<" ";
					}
					decout<<"    ";
				}
				decout<<endl;
			}
		}
	}
	 
	 
	decout<<"\n";
	decout<<"ans_reduce:\n";
	for(i=1;i<=number_lr0;i++)
	{
		if(ans_reduce[i]>0)
		{
			decout<<show_non[ans_reduce[i]]<<" ";
		}
		else decout<<ans_reduce[i]<<" ";	
	}
	decout<<"\n";
	decout<<"ans_back:\n";
	for(i=1;i<=number_lr0;i++)
	{
		decout<<ans_back[i]<<"  ";	
	}
	decout<<"\n";
	decout<<"edge:\n";
	for(i=1;i<=number_lr0;i++)
	{
		decout<<i<<":\n";
		for(int j=1;j<=maxx_num;j++)
		{
			if(ans_edge[i][j])
			{
				if(search_nonterminal[j])
				{
					decout<<show_non[-search_nonterminal[j]]<<":"<<ans_edge[i][j]<<" ";
				}
				else
					decout<<show_ter[j]<<":"<<ans_edge[i][j]<<" ";
			}
			
		}
		decout<<"\n";
	} 
	
}
void write_sentence(int x,string str)
{
	if(x>=0)
	{
		code_out<<"\n";
		while(x)
		{
			code_out<<"	";
			x--;
		}
	}
	code_out<<str;
}
void write_sentence(int x,string str,int temp)
{
	if(x>=0)
	{
		code_out<<"\n";
		while(x)
		{
			code_out<<"	";
			x--;
		}
	}
	code_out<<str<<temp;
} 
void write_code()
{
	code_out.open(output_pro,ios::out|ios::trunc);
	write_sentence(-1,"//需与词法分析器生成的代码相结合");
	write_sentence(0,"#define PDA__count_state ",number_lr0);write_sentence(-1,"//代表项目集的个数");
	write_sentence(0,"#define PDA__count_ele ",maxx_num);write_sentence(-1,"//代表元素(终结符/非终结符)的个数");
	write_sentence(0,"#define PDA__edge_NUM 2146435072//这个常数是计算归约时用，它表示一个int的后11位（不带符号位）的值，//用于计算归约退的距离 ");
	write_sentence(0,"int PDA__stack[1000];//PDA__stack代表所用堆栈 ");
	write_sentence(0,"int PDA__state;//PDA__state代表当前lr状态，为堆栈指针,有值");
	write_sentence(0,"int PDA__success;//如果消耗完了输入串，而且栈只剩该状态，表明无语法错误 ");
	write_sentence(0,"int PDA__end;//该数是表征输入串结束的符号，即为书中的# ");
	write_sentence(0,"int PDA__array[PDA__count_state+1][PDA__count_ele+1];//代表项目集转换表");
	write_sentence(0,"//转换表如为正表示移进，负表示归约，其中前14位表示归约的长度，后面的表示要归约成的项目集 ");
	write_sentence(0,"int PDA__next;//用于记录面对一个元素时要到达的状态");
	write_sentence(0,"int PDA__now;//记录现在所属的状态");
	write_sentence(0,"int PDA__back_num,PDA__reduce_num;//back记录需要退的个数，reduce记录归约成的元素");
	write_sentence(0,"void PDA__upload(int x,int &length,int & destination)//用于解码PDA__array中的负数，即为归约的情况");
	write_sentence(0,"{");
	write_sentence(1,"x=-x;");
	write_sentence(1,"length=(x&PDA__edge_NUM)>>20;");
	write_sentence(1,"if(length)");
	write_sentence(1,"destination=x-(length<<20);");
	write_sentence(1,"else destination=x;");
	write_sentence(0,"}");
	write_sentence(0,"void PDA__init(char* ch)");
	write_sentence(0,"{");
	write_sentence(1,"int i,j;");
	write_sentence(1,"ifstream PDA__cin(ch);");
	write_sentence(1,"PDA__cin>>PDA__success>>PDA__end; ");
	write_sentence(1,"for(i=1;i<=PDA__count_state;i++)");
	write_sentence(1,"{");
	write_sentence(2,"for(j=0;j<=PDA__count_ele;j++)");
	write_sentence(2,"{");
	write_sentence(3,"PDA__cin>>PDA__array[i][j];");
	write_sentence(2,"}");
	write_sentence(1,"}");
	write_sentence(0,"}");
	write_sentence(0,"void PDA__print()//输入堆栈中状态，可以用来debug");
	write_sentence(0,"{");
	write_sentence(1,"for(int i=0;i<=PDA__state;i++)");
	write_sentence(1,"{");
	write_sentence(2,"cout<<PDA__stack[i]<<" ";");
	write_sentence(1,"}");
	write_sentence(1,"cout<<endl;");
	write_sentence(0,"}");
	write_sentence(0,"void PDA__step(int x)");
	write_sentence(0,"{");
	write_sentence(1,"PDA__next=PDA__array[PDA__stack[PDA__state]][x];");
	write_sentence(1,"if(PDA__next>0)");
	write_sentence(1,"{");
	write_sentence(2,"PDA__stack[PDA__state+1]=PDA__next;");
	write_sentence(2,"PDA__state++;");
	write_sentence(2,"flag_token=0;");
	write_sentence(1,"}");
	write_sentence(1,"else if(PDA__next<0)");
	write_sentence(1,"{");
	write_sentence(2,"PDA__upload(PDA__next,PDA__back_num,PDA__reduce_num);");
	write_sentence(2,"PDA__state-=PDA__back_num;");
	write_sentence(2,"PDA__step(PDA__reduce_num);");
	write_sentence(2,"flag_token=1;");
	write_sentence(1,"}");
	write_sentence(1,"else");
	write_sentence(1,"{");
	write_sentence(2,"PDA__now=PDA__stack[PDA__state];");
	write_sentence(2,"if(!PDA__array[temp][0]) ");
	write_sentence(2,"{");
	write_sentence(3,"//error");
	write_sentence(2,"}");
	write_sentence(2,"else");
	write_sentence(2,"{");
	write_sentence(3,"PDA__upload(PDA__array[PDA__now][0],PDA__back_num,PDA__reduce_num);");
	write_sentence(3,"PDA__state-=PDA__back_num;");
	write_sentence(3,"PDA__step(PDA__reduce_num);");
	write_sentence(3,"flag_token=1;");
	write_sentence(2,"}");
	write_sentence(1,"}");
	write_sentence(1,"//PDA__print(); ");
	write_sentence(0,"}");
	write_sentence(0,"void PDA__deal()");
	write_sentence(0,"{");
	write_sentence(1,"flag_token=0;");
	write_sentence(1,"DFA__node temp=now_token();");
	write_sentence(1,"while(temp.num)//如为0则表示可能遇到未定义的特殊字符或者全文分析完毕，以后需要修改分辨这两种状态 ");
	write_sentence(1,"{");
	write_sentence(2,"PDA__step(temp.num);");
	write_sentence(2,"temp=now_token();");
	write_sentence(1,"}");
	write_sentence(1,"while(flag_token)");
	write_sentence(1,"{");
	write_sentence(2,"PDA__step(PDA__end);");
	write_sentence(1,"}");
	write_sentence(0,"}");
	write_sentence(0,"int main()");
	write_sentence(0,"{");
	write_sentence(1,"//这些最好放在处理完DFA的init后");
	write_sentence(1,"PDA__init(\"");write_sentence(-1,output_array);write_sentence(-1,"\");");
	write_sentence(1,"PDA__state=0;");
	write_sentence(1,"PDA__stack[0]=1;");
	write_sentence(1,"PDA__deal();");
	write_sentence(1,"if(PDA__stack[PDA__state]==PDA__success)//仅输出检测结果，可以删除掉");
	write_sentence(1,"{");
	write_sentence(2,"cout<<\"语法检测成功\";");
	write_sentence(1,"}");
	write_sentence(1,"else");
	write_sentence(1,"{");
	write_sentence(2,"cout<<\"语法检测失败\";");
	write_sentence(1,"}");
	write_sentence(1,"cout<<endl;");
	write_sentence(0,"}");
	//write_sentence(,"");
}
