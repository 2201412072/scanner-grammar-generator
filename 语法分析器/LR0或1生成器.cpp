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
//�ó�������LRϵ�з����� 
Ŀǰ���﷨��
1��#terminal id int id int ������
2��#nonterminal id  ������
3��id��id1 id2 ����
	|������ 
4��#left id id  ����;��ʵûɶ�ã�Ĭ�϶������� 
5��#right id id ����;
6��#priority id int id int ����;
7��#result string; 
����3�������Ҫ���ս��Ϊ�����ַ���������/��������ַ������������
nonterminal�ϣ������ڲ��Զ�������ӵ�map��
����7��stringֻ��ȡLR0��LR1��SLR��LALR��֮һ�� 
Ĭ����ʼ�ķ�Ϊ��һ���ķ�

Ŀǰ����ó���ͨ��LL�ķ����ɣ��ķ����£�
S->id: {add(id,point)} C;
	|#terminal A;|#nonterminal B|#left D;|#right E;
	|#priority F;|#result string {result=string} ;
A->id int {map_terminal[id]=int} A|epsilon
B->id {map_nonterminal[id]=-find_int()} B|epsilon
C->id C|single C| '|'C|epsilon
����single�Ǵʷ�������ʶ������ĵ����ַ���˵���������﷨˵������  
D->id D|epsilon
E->id E|epsilon
F->id int F|epsilon


ע�����
1�� ��д����ʽʱ����ʾ�ķ���β��$���ʼ��map�д��ֵΪ
	10086�����Բ�Ҫ��terminal��ֵ��10086�����Ǻ����ڼ���
	cal_firstǰ�Ὣ���޸ĳ�һ�������ġ�ûʹ�ù���ֵ 
2�������Ĭ������ĵ�һ������ʽ��Ϊ��ʼ���ս����Ȼ���
	���һ���²���ʽ�� S__begin ��> S $end�����Բ�Ҫ���ս�
	�������ս�������� $end��S__begin
	��S__begin��map_nonternimal��Ϊ-1��ͬʱ�ò���ʽ��ջ�е�ǰ������λ����0��1��2�� 
3�� ��#terminalʱ������ô�1��ʼ
4�� �ó�����ʶ���ַ�ʱ��̫�Ծ������в���������string���ɱ�
	ʶ��������д����ʱӦС�ģ�ȷ����ʱ�ո�
5���ڴʷ�����ʱ��23�����ȼ���͡� 

 
����������#terminalʱ���õ�id����Ϊ[a-zA-Z0-9]*�������޷�ʶ������һ����bug�����˱��������޸Ĵʷ������� 

��Ŀǰ�о��ʷ���������23����ʵ���ϳ�������Ҳû����23 



a_first�����ڼ�¼һ�����ս�������в���ʽ��ʼ��λ�ã�a_con�����ڼ�¼
һ�����ս����firstʱ���ܸ��µ����з��ս����a�ȼ�¼һ�����ս����stack��
��λ�� 
*/
/*
Ŀǰ���ȣ�
1�������ķ�ͼ 
2����first��  ����//���� 
3����follow��  ����//���� 
4������lr��Ŀ�� ����//���� 
5������lr1��Ŀ��

���ʱ�Ҵ���ȫ�����������Ϊsearch_minus���ս�����������ɵĳ����ٶȻ��һЩ 

һ��ʼlr0��1��Ȼ��ͨ��dfa�������ս������ͨ��edge��ת�ƣ�Ȼ��ͨ��reduce��
�ж��Ƿ��Լ�������Լ��ͨ��back������Ӧ������ջ��ͨ��reduce����Լ��ջ 


6��������Ŀ����lalr��
7������Զ�������
Ŀǰ�뷨��������1���Լ�ʵ��lr��Ŀ������������ת�������Ŀ����
				2��ת��Ϊ�Զ�����ʵ�֣� ���������������״̬��ͬʱ������Ŀ����̫��ת�� 


8��follow������ߣ�slr��
9���������ȼ��ͽ����
Ŀǰ�о����֣� ���ȼ��ͽ���Կ���ͨ����dfa�ı���ʵ�֣�ͬʱdfa���ṩ�����ȼ�
����û�ã��޷����﷨�Ƶ��������ݡ� 

10���ж��Ƿ��г�ͻ 


Ŀǰ��������ջ��һ����stack������¼��ÿ������ʽ������һ����stack_approach
������stack��Ӧλ�ò�Ϊ0ʱ��¼��stack��ʱ����ʽ���ķ��ս����
��stack��Ӧλ��Ϊ0��������¼����һ������ʽ�����һ�����ŵ�λ�� 

Ŀǰ�Ҵ�����дһ��txt������ϸ��Ϣ��д��ȥ������������Ͳ��ùܱ����
�ṩԭ��Ŀ������Ϣɶ���ˣ���ֻ�ñ��ĸ���Ŀ���������������� 

Ŀǰ��׼����ans_back��ans_reduceɾ��������Ϣȫ������ans_edge�� 

*/
FILE *fp;
char *output_pro,*output_array,*output_detail;
char *file_name;
int state,now;//state����ǰ״̬
struct dfa_result_node{
	int result,indicator;
}DFA__s;
queue<dfa_result_node> dfa_result;//dfa_result����Ŀǰʶ������Ľ��
int dfa_array[20][128];
int count_dfa;//count_dfa����dfa��״̬����
int dfa_to[20],dfa_from;//dfa_to����ĳ��״̬�Ƿ�Ϊ����״̬���Լ�����Ӧ���ʲô
struct node {
	int num;
	string content;
};
string show_non[1000];
string show_ter[1000];//������ֻ����������� 
int number_lr0;//lr0��Ŀ���ĸ�������0��ʼ 
int maxx_num;//�����ڼ�¼terminal��ת���������nonterminal�����ֵ�Ƕ��٣�
//�����Ժ��ڽӾ���ʱȷ�����Ĵ�С 
int temp_show;
int cnt;
int point,cnt_first,flag_token,cnt_nonterminal;
int a[100],last[100],location[100];
int a_first[100],last_first[100],location_first[100];
int flag_first=0;//1��ʾ�Ѿ���һ������ʽ�ˣ����ÿ��ǣ��ˣ������ڵ�һ������ʽ��Ҫ�ӣ� 
int flag_ter_c=0;//1��ʾ����ʽ���Ѿ����ս��������ķ��ս��������add_con�ˣ�����Ҳ������£�0����û�� 
int cnt_con=0,a_con[100],last_con[100],y_con[100];
int fa[1000],isright[100],priority[100]={0}; 
int nonidC;//nonidC��S->id:C�е�id��ֵ
int stack[1000];//�ķ�ջ���������0���������ս���������Ƿ��ս�� 
int stack_approach[1000]; 
string strA,strB,strC,strD,strF,result,record_str;
map<string,int> map_terminal,map_nonterminal;
map<int,int> map_epsilon; //map_epsilon�洢stack����Щλ������epsilon������¼��������������ʽ 
//map_terminal�洢����,nonterminal�洢���� 
node nowken;
bitset<100> first_set[100];
bitset<100> temp_first;//���ڼ�¼��ִ��ĳ������ʽʱ�������ó���first�� 

bitset<100> follow_set[100];
bitset<100> temp_follow; 

map<set<int> ,int > map_lr0; 
int search_nonterminal[1000];//��¼��nonterminal���������������Ӧ�ĸ��� 
int search_minus[1000];//��¼��nonterminal��������󣬸�����Ӧ������


int ans_edge[1000][1000];//�ڽӾ��󣬸�����Ľ��
//ת������Ϊ����ʾ�ƽ�������ʾ��Լ������ǰ11λ(��һλ�Ƿ���λ)��ʾ��Լ�ĳ��ȣ�����ı�ʾҪ��Լ�ɵ���Ŀ�� 
int ans_reduce[1000];//��¼ĳһ��Ŀ���Ƿ�ù�Լ,�粻��Ϊ-1������ΪҪ��Լ�ķ��ս������������map_nonterminal�е�ֵ������ȡ����ֵ�� 
int ans_back[1000];//��¼��Լʱ��Ҫ�˵ĳ��� 
int record_PDA_end;//��¼pda����״̬ 

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
	ifstream mycin("�Զ�������_LR_array.txt");
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
		//error();//�����޷����ʷ�������ʶ�� 
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
void add(int x)//add���ڼ�¼һ�����ս�����ķ�ջ�е�����λ�� 
{
	cnt++;
	last[cnt]=a[x];
	location[cnt]=point;
	a[x]=cnt;
}
void add_first(int x)//add_first���ڼ�¼һ�����ս��E�����в���ʽ�Ŀ�ͷ���ķ�ջ�е�λ�� 
{
	cnt_first++;
	last_first[cnt_first]=a_first[x];
	location_first[cnt_first]=point;
	a_first[x]=cnt_first;
}
void add_con(int x,int y)
//add_con��ʾһ�����ս��E�ڲ���ʽ�Ҳ࣬����ͨ�������µ������ս���ļ���
//����˼����������ս���ұ߾Ͳ��ڸü����У� 
{
	cnt_con++;
	last_con[cnt_con]=a_con[x];
	y_con[cnt_con]=y;
	a_con[x]=cnt_con;
}
int find(int x)//���鼯���ҵ�һ��û��ʹ�õ�terminalԪ�� ,fa��¼�˵�һ����ʹ�õ� 
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
	if(temp.num==3||temp.num==23)//23����û�У����Ѿ���T�͸����� 
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
	else if(temp.num==5)//����single 
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
	else if(temp.num==7)//����"|" 
	{
		stack[point]=0;
		point++;
		add_first(nonidC);
		flag_token=0;
		deal_C();
	}
	else if(temp.num==22)//�����������Ϊepsilon�����ֵ���� 
	{
		map_epsilon[point]=nonidC;
		flag_token=0;
		deal_C();
	}
	else if(temp.num==6)//����";" 
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
		flag_ter_c=0;//1��ʾ����ʽ���Ѿ����ս��������ķ��ս��������add_con�ˣ�����Ҳ������£�0����û�� 
		if(!map_nonterminal.count(temp.content))
		{
			//error();
		}
		//add(temp.content);
		nonidC=-map_nonterminal[temp.content];//nonidC��S->id:C�е�id��ֵ,map_nonterminal�д���Ǹ�ֵ 
		if(!flag_first)
		{
			map_nonterminal["S__begin"]=-1;
			add_first(1);
			add_con(nonidC,1);
			stack[point]=-nonidC;//�û���һ������ʽ
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
	map_terminal["$end"]=10086;//10086��Ϊ�˷�����ϣ�����Ҫ�޸� 
	deal_T();
	//�������޸ģ���ֵ����Ҫ������10086 
	i=find(1);
	fa[i]=find(i+1);
	map_terminal["$end"]=i;
	stack[1]=i;
	
	map<string,int>::iterator iter;
	//������ս���Լ����ڳ����д��ֵ 
	cout<<"nonterminal:"<<endl; 
	for(iter=map_nonterminal.begin();iter!=map_nonterminal.end();iter++)
	{
		cout<<(*iter).first<<" "<<(*iter).second<<endl;
		show_non[-(*iter).second]=(*iter).first;
	}
	//����ս���Լ����ڳ����д��ֵ 
	cout<<"\nterminal:"<<endl;
	cout<<"epsilon 0"<<endl;
	for(iter=map_terminal.begin();iter!=map_terminal.end();iter++)
	{
		cout<<(*iter).first<<" "<<(*iter).second<<endl;
		show_ter[(*iter).second]=(*iter).first;
	} 
	cal_stack_approach();
	change_minus();//������������δ����
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
	
	//���first�� 
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
	//���follow�� 
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
	 //���lr0��Ŀ��
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
			else cout<<" :";//epsilon����Ҳ��֪��զ�������Կո���� 
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
void cal_first()//��rebuild��ǰʵ�ֵģ������õľ�ͼ 
{
	int judge[1000],temp_non;
	queue<int> q;//������ֻ��first��ʱ��û��epsilon�ķ��ս�� 
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
	while(!q.empty())//������epsilon 
	{
		int top=q.front();
		q.pop();
		judge[top]=0;
		if(first_set[top][0]) continue;
		for(int k=a_first[top];k;k=last_first[k])//�鿴�����еĲ���ʽ 
		{
			int now_stack=stack[location_first[k]]; 
			if(now_stack==0)//������Բ���epsilon 
			{
				first_set[top][0]=1;//��� 
				for(int j=a_con[top];j;j=last_con[j])//�ҵ����������ܸ��µķ��ս�� 
				{
					if(!judge[y_con[j]]&&!first_set[y_con[j]][0])
					//�����û�ڶ�������,������������epsilon 
					{
						judge[y_con[j]]=1;
						q.push(y_con[j]);//������� 
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
					for(int j=a_con[top];j;j=last_con[j])//�ҵ����������ܸ��µķ��ս�� 
					{
						if(!judge[y_con[j]]&&!first_set[y_con[j]][0])
						//�����û�ڶ�������,������������epsilon 
						{
							judge[y_con[j]]=1;
							q.push(y_con[j]);//������� 
						}
					}
					break;
				}
			}
			else continue;
		}
	}
	//����first�� 
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
		int top=q.front(),flag_first=0;//flag_first�����жϷ��ս���Ƿ���� 
		q.pop();
		judge[top]=0;
		temp_first=first_set[top];
		for(int k=a_first[top];k;k=last_first[k])//�鿴�����еĲ���ʽ 
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
		for(int j=a_con[top];j;j=last_con[j])//�ҵ����������ܸ��µķ��ս�� 
		{
			if(!judge[y_con[j]]&&y_con[j]!=top)
			//�����û�ڶ������� 
			{
				judge[y_con[j]]=1;
				q.push(y_con[j]);//������� 
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
			stack_approach[k]=i-1;//stack_approach�ж�Ӧ��stack��0ʱ������һ������ʽ��ý���,���½�����ַ 
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
			for(k=a[top];k;k=last[k])//���ڲ���ʽ�ұߣ�������߷��ս������q 
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
			for(k=a_first[top];k;k=last_first[k])//���ڲ���ʽ��ߣ����������Բ���ʽ���һ�����ս������q 
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
void cal_edge_epsilon()//��stack��stack_approach�м���������epsilon���ù�Լ��ʲô
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
void cal_SLR() //�������map����set 
{
	int temp_q,k,top,element;
	int temp_end,temp_edge;//temp_edge���ڼ�¼һ����Ŀ���Ƿ��б����� 
	//temp_end���ڼ�¼�Ƿ��в���ʽ�������Լ��м������� 
	bitset<1000> temp_record;//���ڼ�¼ĳһ������ʽ�Ƿ��Ѿ������ 
	bitset<1000> record_element;//��¼һ��lr0��Ŀ����������Ŀ������ʱ���Ƿ��ж�������ʽ��Ӧͬһ��Ԫ�� 
	//number_lr0=1; 
	//queue<node_lr0_point> q_all;//��¼��Ŀ�� 
	queue<set<int> >q_all;//��¼��Ŀ�� 
	queue<int> q_build; // ��¼һ����Ŀ�������еĲ���ʽ
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
				//����Ϊ�˼����һ����Ŀ��Ӧ������ 
				if(record_element[element]) continue;
				record_element[element]=1;
				//���ϼ�¼����Ŀ 
				//temp_edge=0; 
				s.clear();
				//ans_edge[map_lr0[s_top]][element]=;
				s.insert((*iter)+1);
				q_build.push((*iter)+1);
				for(it=iter;it!=s_top.end();it++)
				{
					if(it==iter) continue;
					if(stack[*it]==stack[*iter])//�鿴��һ��Ŀ���Ƿ�����ͬ�ı����������µ������Ŀ���� 
					{
						q_build.push((*it)+1);
						s.insert((*it)+1);
					}
				}
				while(!q_build.empty())//������������Ŀ��չeg S->��E��չE->��a 
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
				temp_edge++;//����һ����Ŀ���й�Լ�ĸ�����������Ӧ��Ϊ1
				if(temp_edge>2)
				{
					//error()
				 } 
				int temp_pro=map_lr0[s_top];//��Ŀ��
				int back_num=0,temp_i=*iter,temp_edge_num;
				if(temp_i==2)
				{
					record_PDA_end=temp_pro;
				}
				temp_i--;
				while(temp_i>=0&&stack[temp_i])//�����Լ��Ҫ��ջ������ 
				{
					temp_i--;
					back_num++;
				}
				if(back_num)
				temp_edge_num=load_edge(back_num,search_minus[stack_approach[(*iter)-1]]);
				//stack_approach[(*iter)-1]��ʾ����Ŀ�������ս�������������д���淶��S->E epsilon W�����޷��ó���ȷ���
				else//����epsilon 
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
							//error//�ƽ���Լ��ͻ 
						}
						else if(ans_edge[temp_pro][temp_record]>0) 
						{
							//error//��Լ��Լ��ͻ 
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
				ans_reduce[rubbish_temp]=stack_approach[rubbish_temp2];//��¼���ս�� 
				k=a_first[ans_reduce[rubbish_temp]];
				while(location_first[k]>rubbish_temp2)
					k=last_first[k];
				k=location_first[k];
				if(k) ans_back[rubbish_temp]=stack_approach[k-1]-k+1;
				else ans_back[rubbish_temp]=2;
			}
			else
			{
				//error��Լ��Լ��ͻ 
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
	//���ջ����Ҳ��֪��ΪɶҪ����� 
	mycout<<point<<endl;
	for(i=0;i<point;i++)
	{
		if(stack[i]<0) mycout<<search_minus[-stack[i]]<<" ";
		else mycout<<stack[i]<<" ";
	}
	mycout<<endl;
	*/
	//�������ж��Ƿ�ɹ��ı�־���Ƿ�����Լ����S__begin�ˣ�S__begin�����־���search_minus[1] 
	mycout<<record_PDA_end;
	mycout<<endl;
	mycout<<map_terminal["$end"]<<endl;
	//number_lr0��maxx_numֱ����Ϊ�궨����������ﲻ������� 
	//mycout<<number_lr0<<" "<<maxx_num<<endl;
	//���lr0�Ƿ�Ӧ�ù�Լ�����Ӧ�ã���������ս��
	//��map_nonterminal�е�ֵ������ȡ����ֵ�� 
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
		for(int j=0;j<=maxx_num;j++)//0Ϊepsilon 
		{
			mycout<<ans_edge[i][j]<<" ";
		}
		mycout<<endl;
	}
}
void write_detail()//����д��ϸ��Ϣ�������û����Ҵ��� 
{
	int i;
	ofstream decout;
	decout.open(output_detail,ios::out|ios::trunc); 
	map<string,int>::iterator iter;
	//������ս���Լ����ڳ����д��ֵ 
	decout<<"nonterminal:"<<endl; 
	for(iter=map_nonterminal.begin();iter!=map_nonterminal.end();iter++)
	{
		decout<<(*iter).first<<" "<<(*iter).second<<endl;
		show_non[-(*iter).second]=(*iter).first;
	}
	//����ս���Լ����ڳ����д��ֵ 
	decout<<"\nterminal:"<<endl;
	//cout<<"epsilon 0"<<endl;
	for(iter=map_terminal.begin();iter!=map_terminal.end();iter++)
	{
		decout<<(*iter).first<<" "<<(*iter).second<<endl;
		show_ter[(*iter).second]=(*iter).first;
	} 
	//������ս�����ս�������ɵĳ����е�ֵ 
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
		//���first�� 
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
		//���follow�� 
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
		 //���lr0��Ŀ��
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
			//���lr0��Ŀ��
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
	write_sentence(-1,"//����ʷ����������ɵĴ�������");
	write_sentence(0,"#define PDA__count_state ",number_lr0);write_sentence(-1,"//������Ŀ���ĸ���");
	write_sentence(0,"#define PDA__count_ele ",maxx_num);write_sentence(-1,"//����Ԫ��(�ս��/���ս��)�ĸ���");
	write_sentence(0,"#define PDA__edge_NUM 2146435072//��������Ǽ����Լʱ�ã�����ʾһ��int�ĺ�11λ����������λ����ֵ��//���ڼ����Լ�˵ľ��� ");
	write_sentence(0,"int PDA__stack[1000];//PDA__stack�������ö�ջ ");
	write_sentence(0,"int PDA__state;//PDA__state����ǰlr״̬��Ϊ��ջָ��,��ֵ");
	write_sentence(0,"int PDA__success;//��������������봮������ջֻʣ��״̬���������﷨���� ");
	write_sentence(0,"int PDA__end;//�����Ǳ������봮�����ķ��ţ���Ϊ���е�# ");
	write_sentence(0,"int PDA__array[PDA__count_state+1][PDA__count_ele+1];//������Ŀ��ת����");
	write_sentence(0,"//ת������Ϊ����ʾ�ƽ�������ʾ��Լ������ǰ14λ��ʾ��Լ�ĳ��ȣ�����ı�ʾҪ��Լ�ɵ���Ŀ�� ");
	write_sentence(0,"int PDA__next;//���ڼ�¼���һ��Ԫ��ʱҪ�����״̬");
	write_sentence(0,"int PDA__now;//��¼����������״̬");
	write_sentence(0,"int PDA__back_num,PDA__reduce_num;//back��¼��Ҫ�˵ĸ�����reduce��¼��Լ�ɵ�Ԫ��");
	write_sentence(0,"void PDA__upload(int x,int &length,int & destination)//���ڽ���PDA__array�еĸ�������Ϊ��Լ�����");
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
	write_sentence(0,"void PDA__print()//�����ջ��״̬����������debug");
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
	write_sentence(1,"while(temp.num)//��Ϊ0���ʾ��������δ����������ַ�����ȫ�ķ�����ϣ��Ժ���Ҫ�޸ķֱ�������״̬ ");
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
	write_sentence(1,"//��Щ��÷��ڴ�����DFA��init��");
	write_sentence(1,"PDA__init(\"");write_sentence(-1,output_array);write_sentence(-1,"\");");
	write_sentence(1,"PDA__state=0;");
	write_sentence(1,"PDA__stack[0]=1;");
	write_sentence(1,"PDA__deal();");
	write_sentence(1,"if(PDA__stack[PDA__state]==PDA__success)//����������������ɾ����");
	write_sentence(1,"{");
	write_sentence(2,"cout<<\"�﷨���ɹ�\";");
	write_sentence(1,"}");
	write_sentence(1,"else");
	write_sentence(1,"{");
	write_sentence(2,"cout<<\"�﷨���ʧ��\";");
	write_sentence(1,"}");
	write_sentence(1,"cout<<endl;");
	write_sentence(0,"}");
	//write_sentence(,"");
}
