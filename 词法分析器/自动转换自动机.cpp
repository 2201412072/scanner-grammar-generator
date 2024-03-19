#include<iostream>
#include<fstream>
#include<map>
#include<vector>
#include<cstring>
#include<queue>
#include<bitset> 
#include<set>
#define len_nfa 64//��ʼnfa״̬�������ֵ 
#define Maxx_dfa 100//�м���̵�dfa������dfa״̬�������ֵ 
#define side_nfa 300//��ʼnfa�ߵĸ������ֵ 
#define alphabet 128//�ַ������ֵ 
#define maxx_define_num 100//�ú궨���������ֵ 
#define maxx_single_def 100//ÿ���궨��������ܹ�������ַ����������ֵ 
using namespace std;
//�����Զ���״̬������c++����
/*
Ŀǰ���﷨�� 
#define ������� eg��#define digit a-zA-Z;
#priority��#pri �������ȼ� eg�� #pri  1  2;��ʾ1�����ȼ�Ϊ2�����ȼ�Խ��Խ���� 
���û��ָ����������DFAʱ����������ͬ�����ȼ��ıȽϣ���������Ȼ���������С�����ȼ���߼������д��� 

���ȼ��������õĳ����Ǳ���(��.*,(���ȼ��ߣ���ôƥ�䵽��ʱ���������߾����ϣ�˵����nfa�д���ͬһ�ڵ㣬
��ʱ����˵Ҫƥ��(,������.*  //�����ͱ�����lex�еıȽ�ģ�������ȼ�˳�򣬸�Ϊ����ȷ�ĸ�ֵ 

epsilon��ʾ�մ� �ַ�����Ϊ128 
digit�ȴ���Ҫ�������ٴ���2 
from number;
to number;
�������ʼ�ڵ����ֹ�ڵ�; 
��������������ʽ eg�� a-e //������[]��Ϊ����c++����Ҫ��[��û��Ū 
ע��Ϊ//��/ ** /(����Ȳ�Ū) 
��ʽ�﷨Ϊ from  to  ����  ��
 ����֮���ÿո��������ʾ�� //define�׶�Ҳ�� 
 //ת���ַ���\����ǰ�� 
 ��Ŀǰ����������\132��ʾ������ֱ�Ӹ�ֵ�����飬������ڵ�LR������֪���в��У� 
(Ŀǰ����128Ϊepsilon�����֣����Բ��ܼ�128)
*/ 

/* 
����
1���ʷ�������
	name_define��¼define��ֵ 
2����ʼnfa��
	num_line��¼nfa���� 
	from��¼���
	to[]��¼����
	next��front��last��¼dfa�ߣ�Ϊ��ʽǰ����
	NFA��¼��ÿ���ߺ��е��ַ� 
3��epsilon�հ�
	bit_epsilon��¼�հ�
4��mid_dfa
	count_dfa��¼mid_dfa�ڵ���
	m_DFA��¼��mid_dfa�ıߣ�Ϊ�ڽӾ��� 
	bit��¼��ÿ��mid_dfa״̬�к��е�nfa״̬ 
4��pri
	pri_num��¼nfa�ڵ����ȼ�
	pri_dfa��¼mid_dfa��ֹ�ڵ㼰��Ӧ��� 
5��hopcroft
	from��¼�����յ�dfa�Ŀ�ʼ״̬ 
	count_h_dfa��¼�����յ�dfa��״̬�� 
	belong_dfa��¼��ÿ��mid_dfa״̬�����ĸ����յ�dfa״̬ 
	final_to��¼���յ�dfa����״̬����Ӧ���
	final_DFA��¼�����յ�dfa�ı����ӷ�ʽ������Ϊ�ڽӾ��� 
*/
//def����¼name_define 
struct def{
	int c[maxx_single_def];//256�����������ģ�256���⣬��257��ʾ name_define[1]��������� 
	int num=0;//c�ĳ��ȣ�c��¼��define������ַ� 
};
struct node{
	int from,to;//��ֹ�ڵ� 
	bool operator <(const node &t)const
	{
		if(from!=t.from) return from<t.from;
		if(to!=t.to) return to<t.to;
	}
};
struct bit_dfa{
	bitset<len_nfa> b;
	bool operator <(const bit_dfa &t) const
	{
		//return b.count()<t.b.count();
		int i;
		for(i=len_nfa-1;i>=0;i--)
		{
			if(b[i]==t.b[i]) continue;
			else return b[i]<t.b[i];
		}
		return 0; 
	}
};

FILE *fp; 
char *file_name,*output,*array;
//-----�ʷ�����------
//(from��������final_from�ļ�¼��to������pri_error�� 
//flag���ڴʷ������׶� 
int flag_from=0,flag_define=0,flag_fu=0,flag_to=0,flag_sen=0;
int flag_shuzi=0;
int flag_end=0,flag_pri=0,flag_fenhao=0,flag_ceshi;
/*
flag_fu����
1��a-Z���֣���Ҫѭ������
2�����������ַ�
3��\t����ת���ַ� 
*/
//��¼from�����˼��� 
int num_from=0;
//cnt��ʾname_define�ĳ��ȣ�c_store������ȡtoken��from��� 
//��hopcrft��from�ͱ�ʾ���յ�dfa��from 
int cnt=0,c_store=-1,from=-1;
//p_to��ʾ�յ������n��ʾ����������״̬�� 
int p_to=0,n;
//temp_pri�����ٴʷ�����ʱ�������ȼ��ĵ�һ������ڵ�
int temp_pri; 
//to��ʾ�յ�,���Ǽ�¼��to�ı�� 
int to[len_nfa];
//��¼NFA����ʱ���� 
node point;
//define����ʽ 
def name_define[maxx_define_num];
//��¼define����ʽ�����֣��������ֵ 
map<string, int> mapp; 

//-----��epsilon�հ�------- 
//element��¼���д����г��ֵ�״̬ 
bool element[len_nfa*3];
//bit_epsilon���ڼ�¼x��epsilon�հ������е�iλ����i���ڵ� 
bitset<len_nfa> bit_epsilon[len_nfa]; 

//------NFAת��ΪDFA----- 
//��zifu������hop_next�� 
//�ַ���¼�������õ��������ַ�
set<int> zifu;
//num_line��ʾNFA����ʽ�ĸ���
int num_line=0;
//��������NFA������ͼ 
int next[side_nfa],front[len_nfa],last[side_nfa];
//��¼NFA����ʽ�е��ַ�(�ĳ�bitset) 
//������nfaһ���ߵı�ţ�����¼�������ϵ��ַ� 
bitset<alphabet+1> NFA[side_nfa];
//count_dfa��ʾdfa�ڵ�ĸ��� 
int count_dfa=0;
//m_DFA��ʾmid_DFA�����м���̣�
//m_DFA[i][c]��ʾdfa��i�������ͨ���ַ�c�����ĸ��ڵ� 
int m_DFA[Maxx_dfa][alphabet];
//����û����n,���е�iλ����i���ڵ�,��ʾ������dfa��״̬������nfa 
bitset<len_nfa> bit[Maxx_dfa];

//----pri_error------
//pri_num���ڶ�������ڵ�����ȼ�����ʼĬ��Ϊ0 
int pri_num[len_nfa];
//pri_dfa���ڼ�¼ÿ��dfa�յ�ڵ��Ҫ��Ӧ��nfa�ڵ� 
//pri_dfa��˳���¼����ֹ�ڵ��ˣ���Ϊ�����ȼ��Ŀ϶�����ֹʱ�� 
int pri_dfa[Maxx_dfa]; 

//-----hopcroft�Լ�hop_next------ 
//final_to��ʾ���յ�dfa���յ㣬����¼��ÿ���ڵ��Ƿ����յ�,�Լ�����ǣ������ʲô 
int final_to[Maxx_dfa];
//final_DFA[i][c]��ʾdfa��i�������ͨ���ַ�c�����ĸ�
int final_DFA[Maxx_dfa][alphabet]; 
//count_h_dfa��¼hopcroft��ڵ���� 
int count_h_dfa=0; 
//belong_dfa��¼mid_dfa���ļ����ڵ�����final_dfa���ĸ��ڵ� 
int belong_dfa[Maxx_dfa];

ofstream mycout;

string get_token()
{
	string temp="";
	int c;
	flag_end=0;
	flag_fu=2;
	flag_fenhao=0;
	if(c_store==-1)
	{
		c=fgetc(fp);
	}
	else
	{
		c=c_store;
		c_store=-1;
	}
	while(temp==""&&c!=EOF)
	{
		while(c!='\r'&&c!=EOF&&c!='\t'&&c!='\n'&&c!=' ')
		{
			if(c==';'&&temp!="")
			{
				/*if(!flag_fenhao)//���Լ�¼��;������֪�����в� 
				{
					c_store=c;
					flag_end=1;
					break;
				}
				else
				{
					flag_fenhao=0;
				}*/
				if(flag_fenhao&&!flag_shuzi)
				{
					flag_fenhao=0;
				}
				else
				{
					c_store=c;
					flag_end=1;
					break;
				}
			}
			if(c=='\\')
			{
				if(flag_fu==1)
				{
					cout<<"[ERROR]get_token::1�����ַ���ʽ����"<<endl;
				}
				flag_fu=3;
				flag_fenhao=1;
			}
			else if(c=='-')
			{
				if(flag_fu==3)
				{
					cout<<"[ERROR]get_token::2�����ַ���ʽ����"<<endl;
				}
				flag_fu=1;
			}
			else if(c>='0'||c<='9')
			{
				flag_shuzi=1;
			}
			temp.push_back(c);
			c=fgetc(fp);
		}
		flag_shuzi=0;
		if(!flag_end)
		{
			c=fgetc(fp);
			c_store=c;
		}
	}
	return temp;
}
void deal();//��� 
void add(int *c,int &num,int x);//����defineʱ�� 
void add(bitset<alphabet+1> &b,int x);//��define����c�� ������NFAʱ�� 
void add(int x,int y);//�ӱ�(�˴������Ǵ�1��ʼ,������ȫ��0��ʼ����Ϊ�����ʼ����ֻ֧��1��ʼ�� 
void analyse(int *c,int &num,string token);//����defineʱ�� 
void analyse(bitset<alphabet+1> &b,string token);//����NFAʱ�� 
void find_set_epsilon(int x);//Ѱ��epsilon�հ� 
void NFAtoDFA();
void pri_error();//�鿴���ȼ��Ƿ�����ͻ 
void hopcroft();
void hop_next();//������hopcroft�������Լ�from��to����������
void write_dfa_array();//����дfinal_dfa�����Լ�final_from��final_to���� 
void write_code(); //����д���� 
int toint(string str)
{
	int i,ans=0;
	for(i=0;i<str.length();i++)
	{
		if(str[i]>='0'&&str[i]<='9')
		{
			ans*=10;
			ans+=str[i]-'0';
		}
		else
		{
			return -1;
		}
	}
	return ans;
}
int main()
{
	file_name="�Զ�������_LR.txt";
	int len=strlen(file_name);
	output=new char[len+4];
	array=new char[len+6];
	strcpy(output,file_name);
	strcpy(array,file_name);
	output[len-4]='_',output[len-3]='d';
	output[len-2]='f',output[len-1]='a';
	output[len]='.',output[len+1]='t';
	output[len+2]='x',output[len+3]='t';
	array[len-4]='_',array[len-3]='a',array[len-2]='r';
	array[len-1]='r',array[len]='a',array[len+1]='y';
	array[len+2]='.',array[len+3]='t',array[len+4]='x';
	array[len+5]='t';
	//cout<<output<<endl; 
	fp=fopen(file_name,"r");
	string token=get_token();
	for(int i=0;i<side_nfa;i++)
	{
		next[i]=-1;
	}
	for(int i=0;i<Maxx_dfa;i++)
	{
		next[i]=belong_dfa[i]=pri_dfa[i]=final_to[i]=-1;
		for(int j=0;j<alphabet;j++)
		{
			final_DFA[i][j]=-1;
			m_DFA[i][j]=-1;
		}
	}
	while(token!="")
	{
		//cout<<token<<endl;
		if(token=="#define")
		{
			flag_define=1;
			token=get_token();
			continue;
		}
		if(token==";")
		{
			if(flag_sen==2)
			{
				deal();
				num_line++;
				add(point.from,point.to);
			}
			flag_define=0;
			flag_sen=0;
			flag_from=0;
			flag_to=0;
			flag_pri=0;
			flag_shuzi=0;
			token=get_token();
			continue;
		}
		if(token=="from")
		{
			num_from++;
			if(num_from>=2)
			{
				cout<<"[ERROR]main::1������̫���from״̬"<<endl;
			}
			flag_from=1;
			token=get_token();
			continue;
		}
		if(token=="to")
		{
			flag_to=1;
			token=get_token();
			continue;
		}
		if(token=="#priority"||token=="#pri")
		{
			flag_pri=1;
			token=get_token();
			continue;
		} 
		if(flag_from==1)
		{
			flag_from=0;
			from=toint(token);
			if(from==-1)
			{
				cout<<"[ERROR]main2:from״̬����Ϊһ������"<<endl;
			}
			else if(from>=len_nfa)
			{
				cout<<"[ERROR]main3:״̬������󣬿����޸ĳ����е�len_nfaֵ"<<endl;
			} 
			flag_from=-1;
			token=get_token();
			continue;
		}
		
		if(flag_to==1)
		{
			flag_to=0;
			to[p_to]=toint(token);
			if(to[p_to]==-1)
			{
				cout<<"[ERROR]main4:to״̬����Ϊһ������"<<endl;
			}
			else if(to[p_to]>=len_nfa)
			{
				cout<<"[ERROR]main5:״̬������󣬿����޸ĳ����е�len_nfaֵ"<<endl;
			} 
			p_to++;
			if(p_to>=len_nfa)
			{
				cout<<"[ERROR]main6:�����to״̬���࣬�����޸ĳ����е�len_nfaֵ"<<endl;
			}
			token=get_token();
			continue;
		}
		
		if(flag_define==1)
		{
			flag_define=2;
			if(token.length()==1)
			{
				cout<<"[ERROR]main7:define�к�����������ӦΪ2�������޷��뵥�ַ�����"<<endl;
			}
			cnt++;
			if(cnt>=maxx_define_num) 
			{
				cout<<"[ERROR]main8:�����define���࣬�����޸ĳ�����maxx_define_num��ֵ"<<endl;
			}
			mapp[token]=cnt;
			token=get_token();
			continue;
		}
		else if(flag_define==2||flag_define==3)
		{
			flag_define=3;
			analyse(name_define[cnt].c,name_define[cnt].num,token);
			token=get_token();
			continue;
		}
		if(flag_pri==1)
		{
			temp_pri=toint(token);
			if(temp_pri>=len_nfa)
			{
				cout<<"[ERROR]main9:״̬������󣬿����޸ĳ����е�len_nfaֵ"<<endl;
			}
			flag_pri=2;
			token=get_token();
			continue;
		}
		else if(flag_pri==2)
		{
			int temp=toint(token);
			if(temp<0)
			{
				cout<<"[ERROR]main10:���ȼ�����Ϊ��"<<endl;
			 } 
			pri_num[temp_pri]=temp;
		}
		if(flag_sen==0)
		{
			
			point.from=toint(token);
			n=n>point.from?n:point.from;
			if(n>=len_nfa)
			{
				cout<<"[ERROR]main11:״̬������󣬿����޸ĳ����е�len_nfaֵ"<<endl;
			} 
			element[point.from]=1;
			flag_sen=1;
			token=get_token();
			continue;
		}
		else if(flag_sen==1)
		{
			point.to=toint(token);
			n=n>point.to?n:point.to;
			if(n>=len_nfa)
			{
				cout<<"[ERROR]main12:״̬������󣬿����޸ĳ����е�len_nfaֵ"<<endl;
			}
			element[point.to]=1;
			flag_sen=2;
			token=get_token();
			continue;
		}
		else if(flag_sen==2)
		{
			analyse(NFA[num_line],token);
			token=get_token();
			continue;
		}
		else
		{
			cout<<"[ERROR]main13:�޷�ʶ��÷���"<<endl;
		 } 
	}
	for(int i=0;i<=n;i++)
	{
		if(element[i])
		{
			find_set_epsilon(i);
		}
	}
	//���ÿ���ڵ��epsilon�հ�����bitset��ʽ 
	cout<<"epsilon:"<<endl;
	for(int i=0;i<=n;i++)
	{
		cout<<bit_epsilon[i]<<endl;
	}/**/
	NFAtoDFA();
	//���mid_DFA��ÿ��״̬��������nfa��״̬ 
	cout<<"bit:"<<endl;
	for(int i=0;i<count_dfa;i++)
	{
		//cout<<bit[i]<<endl;
		cout<<i<<":\t";
		for(int j=0;j<len_nfa;j++)
		{
			if(bit[i][j])
			{
				cout<<j<<" ";
			}
		}
		cout<<endl;
		
	}/**/
	//���mid_DFA�Ľڵ��Լ���ʶ����ַ����ܵ���Ľڵ� 
	cout<<"m_DFA:"<<endl;
	for(int i=0;i<count_dfa;i++)
	{
		cout<<i<<":"<<endl;
		for(int j=0;j<128;j++)
		{
			if(m_DFA[i][j]!=-1)
			{
				cout<<(char)j<<":"<<m_DFA[i][j]<<" ";
			}
		}
		cout<<endl;
	} /**/
	pri_error();
	//����յ����Լ����ȼ� 
	cout<<"pri_dfa:"<<endl;
	for(int i=0;i<count_dfa;i++)
	{
		if(pri_dfa[i])
		{
			cout<<i<<":"<<pri_dfa[i]<<endl;
		}
	}/**/
	hopcroft();
	hop_next(); 
	cout<<"belong_DFA:"<<endl;
	for(int i=0;i<count_dfa;i++)
	{
		cout<<belong_dfa[i]<<" ";
	}
	cout<<endl;/**/
	set<int>::iterator iter=zifu.begin(); 
	cout<<"final_DFA:"<<endl;
	for(int i=0;i<count_h_dfa;i++)
	{
		cout<<i<<":"<<endl;
		for(iter=zifu.begin();iter!=zifu.end();iter++)
		{
			if(final_DFA[i][*iter]!=-1)
			cout<<(char)*iter<<":"<<final_DFA[i][*iter]<<" ";
		}
		cout<<endl;
	}/**/
	cout<<"final_to:"<<endl;
	for(int i=0;i<count_h_dfa;i++)
	{
		if(final_to[i])
		{
			cout<<i<<":"<<final_to[i]<<endl;
		}
	}/**/
	write_dfa_array();
	write_code(); 
} 
 void analyse(int *c,int &num,string token)
 {
 	int len=token.length();
			if(len==1)
			{
				c[num]=token[0];
				num++;
			}
			else if(len==2)
			{
				if(flag_fu==3)
				{
					c[num]=token[1];
					num++;
				}
				else
				{
					if(mapp.count(token)==0)
					{
						//error;
						cout<<"[ERROR]anaylse1:���� "<<token<<" ������"<<endl;
					}
					else
					{
						add(c,num,mapp[token]);
					}
				}
			}
			else if(len==3)
			{
				if(flag_fu==1)
				{
					for(int i=token[0];i<=token[2];i++)
					{
						c[num]=i;
						num++;
					}
				}
				else
				{
					if(mapp.count(token)==0)
					{
						//error;
						cout<<"[ERROR]analyse2:���� "<<token<<" ������"<<endl;
					}
					else
					{
						add(c,num,mapp[token]);
					}
				}
			}
			else
			{
				if(token=="epsilon")
				{
					c[num]=128;
					num++;
				 } 
				 else if(mapp.count(token)==0)
				{
					//error;
					cout<<"[ERROR]analyse3:���� "<<token<<" ������"<<endl;
				}
				else
				{
					add(c,num,mapp[token]);
				}
			}
}
void analyse(bitset<alphabet+1> &b,string token)
{
	int len=token.length();
	if(len==1)
	{
		b.set(token[0]);
		zifu.insert(token[0]);
	}
	else if(token[0]=='\\')
	{
		if(token[1]<'0'||token[1]>'9')
		{
			if(flag_fu==3)
			{
				b.set(token[1]);
				zifu.insert(token[1]);
			}	
		}
		else
		{
			cout<<"token!!! "<<token<<"  "<<len<<endl;
			int temp=toint(token.substr(1,len-1));
			if(temp==128) 
			{
				cout<<"[ERROR]anaylse4:128Ϊepsilon��ֵ������������������;"<<endl;
			}
			b.set(temp);
			zifu.insert(temp);
		}
	}
	else if(len==2)
	{
		if(mapp.count(token)==0)
		{
			//error;
			cout<<"[ERROR]analyse5:���� "<<token<<" ������"<<endl;
		}
		else
		{
			add(b,mapp[token]);
		}
	}
	else if(len==3)
	{
		if(flag_fu==1)
		{
			for(int i=token[0];i<=token[2];i++)
			{
				b.set(i);
				zifu.insert(i);
			}
		}
		else
		{
			if(mapp.count(token)==0)
			{
				//error;
				cout<<"[ERROR]analyse5:���� "<<token<<" ������"<<endl;
			}
			else
			{
				add(b,mapp[token]);
			}
		}
	 }
	else
	{
		if(token=="epsilon")
		{
			b.set(128);
		}
		else if(mapp.count(token)==0)
		{
			//error
			cout<<"[ERROR]analyse6:���� "<<token<<" ������"<<endl;
		}
		else
		{
			add(b,mapp[token]);
		}
	} 
		
}
 void deal()
 {
 	
 	cout<<point.from<<" "<<point.to<<" "<<endl;
 	for(int i=1;i<=alphabet;i++)
 	{
 		if(NFA[num_line][i])
 		cout<<i<<" ";//�����鿴�ַ���������(char)i�滻i���˴���Ϊ��LRʱ����ʹ������ 
	 }
	 cout<<endl;
 }
void add(int *c,int &num,int x)
{
	int i;
	for(i=0;i<name_define[x].num;i++)
	{
		if(name_define[x].c[i]<=alphabet)
 		{
 			c[num]=name_define[x].c[i];
 			num++;
		}
		 else
		 {
		 	add(c,num,name_define[x].c[i]-256);
		 }
	}
}
void add(bitset<alphabet+1> &b,int x)
{
	int i;
	for(i=0;i<name_define[x].num;i++)
	{
		if(name_define[x].c[i]<=alphabet)
		{
			b.set(name_define[x].c[i]);
			if(name_define[x].c[i]<alphabet) 
			zifu.insert(name_define[x].c[i]);
		}
		else
		{
			add(b,name_define[x].c[i]-256);
		}
	}
} 

void add(int x,int y)
{
	last[num_line]=front[x];
	front[x]=num_line;
	next[num_line]=y;
}

void find_set_epsilon(int x)
{
	int k;
	//temp_NFA������epsilon�հ� 
	bool temp_NFA[len_nfa];
	queue<int>q;
	q.push(x);
	memset(temp_NFA,0,sizeof(temp_NFA));
	temp_NFA[x]=1;
	while(!q.empty())
	{
		int top=q.front();
		q.pop();
		for(k=front[top];next[k]!=-1;k=last[k])
		{
			if(!temp_NFA[next[k]]&&NFA[k-1][128])
			{
				temp_NFA[next[k]]=1;
				q.push(next[k]);
			}
		}
	}
	for(int i=0;i<=n;i++)
	{
		if(temp_NFA[i])
		{
			bit_epsilon[x].set(i);
			//bit_epsilon���ڼ�¼x��epsilon�հ������е�iλ����i-1���ڵ� 
		}	
	}
}
void NFAtoDFA()
{
	//���ڸ�bitset�������Լ���һ���Ƚ�bitset�ķ��� 
	flag_ceshi=1;
	map<bit_dfa,int> map_bit;
	queue<bitset<len_nfa> >q;//��¼NFAepsilon���� 
	//bitset<128> bit_temp;//��¼�ַ�
	queue<int> bianhao; 
	bitset<len_nfa> bit_temp;
	bit_dfa temp;
	temp.b=bit[count_dfa]=bit_epsilon[from];
	map_bit[temp]=0;
	count_dfa++;
	q.push(bit[0]);
	bianhao.push(0);
	while(!q.empty())
	{
		bitset<len_nfa> top_b=q.front();
		int top_bianhao=bianhao.front();
		q.pop();
		bianhao.pop();
		
		set<int>::iterator iter=zifu.begin();
		for(;iter!=zifu.end();iter++)
		{
			bit_temp.reset();
			for(int i=0;i<=n;i++)
			{
				if(top_b[i])
				{
					int k;
					for(k=front[i];k>0&&next[k]!=-1;k=last[k])
					{
						if(NFA[k-1][*iter])
						{
							bit_temp|=bit_epsilon[next[k]];
							//cout<<bit_temp<<endl;
						}
					}
				}
			}
			if(!bit_temp.any()) continue;
			temp.b=bit_temp;
			if(map_bit.count(temp)==0)
			{
				q.push(bit_temp);
				bianhao.push(count_dfa);
				bit[count_dfa]=bit_temp;
				m_DFA[top_bianhao][*iter]=count_dfa;
				map_bit[temp]=count_dfa;
				count_dfa++;
				if(count_dfa>=Maxx_dfa)
				{
					cout<<"[ERROR]NFAtoDFA1:ת���ɵ�dfa״̬���࣬�����޸ĳ����Maxx_dfa��ֵ"<<endl;
				 } 
			}
			else
			{
				int state=map_bit[temp];
				m_DFA[top_bianhao][*iter]=state;
			}
		}
	}
}
void pri_error()
{
	int i,j,k,last_node,maxx=0,count_num=1;
	bitset<len_nfa> b,temp;
	//error_pri��¼�˴�������ȼ�nfa�ڵ� 
	vector<int> error_pri;
	for(i=0;i<p_to;i++)
	{
		b.set(to[i]);
	}
	for(i=0;i<count_dfa;i++)
	{
		temp=bit[i]&b;
		error_pri.clear();
		maxx=0;
		count_num=1;
		if(temp.count()==0)
		{
			continue;
		}
		else if(temp.count()==1)
		{
			for(j=0;j<=n;j++)
			{
				if(temp[j])
				{
					last_node=j;
					break;
				}
			}
			pri_dfa[i]=last_node;
			continue;
		}
		for(j=0;j<=n;j++)
		{
			if(temp[j])
			{
				if(maxx<pri_num[j])
				{
					maxx=pri_num[j];
					error_pri.clear(); 
					last_node=j;
					count_num=1;
				}
				else if(maxx==pri_num[j])
				{
					count_num++;
					last_node=j;
					error_pri.push_back(j);
				}
			}
		}
		if(count_num>1)
		{
			//error;
			cout<<"[ERROR]pri_error:δ����"; 
			cout<<error_pri[0];
			for(j=1;j<error_pri.size();j++)
			{
				cout<<","<<error_pri[j];
			}
			cout<<"֮������ȼ������½�����������ԡ�"<<endl;
		}
		pri_dfa[i]=last_node; 
	}
}
void hopcroft()
{
	count_h_dfa=0;
	map<int,int> map_temp_dfa;
	map<int,int> map_temp_hop;
	/*
	record���ڼ�¼Ŀǰͨ���ڼ����ַ��ָ�ģ���Ϊ��Ҫ�Ƿָ�
	N�����������Ƕ��Ǵ�һ�������зָ����ģ�������ĸ�����
	�ָ��ַ���c��ʼ����ô���������Ӽ���û��Ҫ��ȥ��a��b����
	�޷����зָ 
	*/ 
	int record[Maxx_dfa],temp,belong_temp[Maxx_dfa];
	queue<int> q;
	for(int i=0;i<count_dfa;i++)
	{
		{
			if(!map_temp_dfa.count(pri_dfa[i]))
			{
				map_temp_dfa[pri_dfa[i]]=count_h_dfa;
				belong_dfa[i]=count_h_dfa;
				count_h_dfa++;
				if(count_h_dfa>=Maxx_dfa)
				{
					cout<<"[ERROR]hopcroft1:ת���ɵ�dfa״̬���࣬�����޸ĳ����Maxx_dfa��ֵ"<<endl;
				 } 
			}
			else
			{
				belong_dfa[i]=map_temp_dfa[pri_dfa[i]];
			}
		}
	}
	for(int i=0;i<count_h_dfa;i++)
	{
		q.push(i);
	}
	memset(record,0,sizeof(record));
	while(!q.empty())
	{
		int top=q.front(),size=0;
		q.pop();
		for(int i=0;i<count_dfa;i++)
		{
			if(belong_dfa[i]==top) size++;
		}
		if(size==1) continue;
		for(int k=record[top];k<alphabet;k++)
		{
			map_temp_hop.clear();
			memset(belong_temp,-1,sizeof(belong_temp));
			size=0;
			for(int j=0;j<count_dfa;j++)
			{
				if(belong_dfa[j]!=top) continue;
				if(m_DFA[j][k]==-1) temp=-1;
				else
					temp=belong_dfa[m_DFA[j][k]];
				if(!map_temp_hop.count(temp))
				{
					if(size==0)
					{
						map_temp_hop[temp]=top;
						size++;
					}
					
					else
					{
						map_temp_hop[temp]=count_h_dfa;
						count_h_dfa++;
						if(count_h_dfa>=Maxx_dfa)
						{
							cout<<"[ERROR]hopcroft2:ת���ɵ�dfa״̬���࣬�����޸ĳ����Maxx_dfa��ֵ"<<endl;
				 		}
						size++;
					}
				}
			}
			if(size==1) continue;
			else
			{
				for(int j=0;j<count_dfa;j++)
				{
					if(belong_dfa[j]!=top) continue;
					if(m_DFA[j][k]==-1) temp=-1;
					else temp=belong_dfa[m_DFA[j][k]];
					belong_temp[j]=map_temp_hop[temp];
					record[j]=k;
				}
				for(int j=0;j<count_dfa;j++)
				{
					if(belong_temp[j]!=-1)
					{
						belong_dfa[j]=belong_temp[j];
					}
				}
				map<int,int>::iterator iter=map_temp_hop.begin();
				for(;iter!=map_temp_hop.end();iter++)
				{
					q.push(iter->second);
				}
				break;
			}
		}
	}
}
void hop_next()//������hopcroft�������Լ�from��to���������� 
{
	from=belong_dfa[0];
	for(int i=0;i<count_dfa;i++)
	{
		set<int>::iterator iter=zifu.begin();
		for(;iter!=zifu.end();iter++)
		{
			if(m_DFA[i][*iter]!=-1)
			{
				final_DFA[belong_dfa[i]][*iter]=belong_dfa[m_DFA[i][*iter]];
			}
		}
		if(pri_dfa[i]!=-1)
		{
			final_to[belong_dfa[i]]=pri_dfa[i]; 
		}
	}
}
//Ŀǰ���õ�final_DFA�ڽӾ���count_h_dfa�ڵ������
//from��㣬final_to�յ��Լ���Ҫ�����
void write_dfa_array()
{
	ofstream mycout;
	mycout.open(array,ios::out|ios::trunc);
	int i;
	mycout<<count_h_dfa<<endl;
	for(i=0;i<count_h_dfa;i++)
	{
		for(int j=0;j<alphabet;j++)
		{
			mycout<<final_DFA[i][j]<<" ";//final_DFA���ޱ���Ϊ-1 
		}
		mycout<<endl;
	}
	mycout<<from<<endl;//дfinal_from 
	for(i=0;i<count_h_dfa;i++)//дfinal_to 
	{
		mycout<<final_to[i]<<" ";//final_to�粻Ϊto��Ϊ-1 
	}
	mycout.close();
} 
void write_sentence(int x,int temp)
{
	if(x>=0)
	{
		mycout<<"\n";
		while(x)
		{
			mycout<<"	";
			x--;
		}
	}
	mycout<<temp;
}
void write_sentence(int x,string str)
{
	if(x>=0)
	{
		mycout<<"\n";
		while(x)
		{
			mycout<<"	";
			x--;
		}
	}
	mycout<<str;
}
void write_sentence(int x,string str,int temp)
{
	if(x>=0)
	{
		mycout<<"\n";
		while(x)
		{
			mycout<<"	";
			x--;
		}
	}
	mycout<<str<<temp;
} 
void write_code()
{
	mycout.open(output,ios::out|ios::trunc);
	ifstream mycin(array);
	int i;
	write_sentence(-1,"#include<fstream>");
	write_sentence(0,"#include<stack>");
	write_sentence(0,"#include<iostream>");
	write_sentence(0,"#include<queue>");
	write_sentence(0,"using namespace std;");
	write_sentence(0,"int DFA__state;//DFA__state����ǰ״̬");
	write_sentence(0,"struct DFA__result_node{");
	write_sentence(1,"int result,indicator;");
	write_sentence(0,"}DFA__s;");
	write_sentence(0,"queue<DFA__result_node> DFA__result;//DFA__result����Ŀǰʶ������Ľ��");
	write_sentence(0,"int DFA__array[",count_h_dfa+1);write_sentence(-1,"][",alphabet);write_sentence(-1,"];");
	write_sentence(0,"int count_DFA;//count_DFA����DFA��״̬����");
	write_sentence(0,"int DFA__to[",count_h_dfa+1);
	write_sentence(-1,"],DFA__from;//DFA__to����ĳ��״̬�Ƿ�Ϊ����״̬���Լ�����Ӧ���ʲô");
	write_sentence(0,"struct DFA__node {");
	write_sentence(1,"int num;");
	write_sentence(1,"string content;");
	write_sentence(0,"};");
	write_sentence(0,"string DFA__record_str;");
	write_sentence(0,"DFA__node nowken;");
	write_sentence(0,"int flag_token;//���Ϊ1����ʾ������һ�����������ԭ�ȵ�");
	write_sentence(0,"void DFA__init()");
	write_sentence(0,"{");
	write_sentence(1,"int i,j;");
	write_sentence(1,"ifstream DFA__mycin(\"");write_sentence(-1,array);write_sentence(-1,"\");");
	write_sentence(1,"DFA__mycin>>count_DFA;");
	write_sentence(1,"for(i=0;i<count_DFA;i++)");
	write_sentence(1,"{");
	write_sentence(2,"for(j=0;j<",alphabet);write_sentence(-1,";j++)");
	write_sentence(2,"{");
	write_sentence(3,"DFA__mycin>>DFA__array[i][j];");
	write_sentence(2,"}");
	write_sentence(1,"}");
	write_sentence(1,"DFA__mycin>>DFA__from;");
	write_sentence(1,"for(i=0;i<count_DFA;i++)");
	write_sentence(1,"{");
	write_sentence(2,"DFA__mycin>>DFA__to[i];");
	write_sentence(1,"}");
	write_sentence(0,"}");
	write_sentence(0,"void DFA__deal_state(string &str)");
	write_sentence(0,"{");
	write_sentence(1,"DFA__s.indicator=-1;");
	write_sentence(1,"DFA__s.result=-1;");
	write_sentence(1,"int DFA__now=0;");
	write_sentence(1,"DFA__record_str=\"\";");
	write_sentence(1,"int l=str.size();");
	write_sentence(1,"DFA__state=DFA__from;");
	write_sentence(1,"while(DFA__now<l)");
	write_sentence(1,"{");
	write_sentence(2,"if(DFA__to[DFA__state]!=-1)");
	write_sentence(2,"{");
	write_sentence(3,"DFA__s.indicator=DFA__now;");
	write_sentence(3,"DFA__s.result=DFA__to[DFA__state];");
	write_sentence(2,"}");
	write_sentence(2,"if(DFA__array[DFA__state][str[DFA__now]]==-1)");
	write_sentence(2,"{");
	write_sentence(3,"DFA__record_str=str.substr(DFA__now);");
	write_sentence(3,"break;");
	write_sentence(2,"}");
	write_sentence(2,"DFA__state=DFA__array[DFA__state][str[DFA__now]];");
	write_sentence(2,"DFA__now++;");
	write_sentence(1,"}");
	write_sentence(1,"if(DFA__to[DFA__state]!=-1)");
	write_sentence(1,"{");
	write_sentence(2,"DFA__s.result=DFA__to[DFA__state];");
	write_sentence(2,"DFA__s.indicator=DFA__now;");
	write_sentence(1,"}");
	write_sentence(0,"}");
	write_sentence(0,"DFA__node get_token()");
	write_sentence(0,"{");
	write_sentence(1,"string str;");
	write_sentence(1,"if(DFA__record_str==\"\")");
	write_sentence(1,"{");
	write_sentence(2,"cin>>str;");
	write_sentence(2,"DFA__deal_state(str);");
	write_sentence(1,"}");
	write_sentence(1,"else");
	write_sentence(1,"{");
	write_sentence(2,"str=DFA__record_str;");
	write_sentence(2,"DFA__deal_state(str);");
	write_sentence(1,"}");
	write_sentence(1,"DFA__node ans_get;");
	write_sentence(1,"if(DFA__s.result==-1)");
	write_sentence(1,"{");
	write_sentence(2,"//error();//�����޷����ʷ�������ʶ�� ");
	write_sentence(2,"ans_get.num=0;");
	write_sentence(2,"ans_get.content=\"\";");
	write_sentence(1,"}");
	write_sentence(1,"else");
	write_sentence(1,"{");
	write_sentence(2,"ans_get.num=DFA__s.result;");
	write_sentence(2,"ans_get.content=str.substr(0,DFA__s.indicator);");
	write_sentence(1,"}");
	write_sentence(1,"return ans_get;");
	write_sentence(0,"}");
	write_sentence(0,"DFA__node now_token()");
	write_sentence(0,"{");
	write_sentence(1,"if(!flag_token)");
	write_sentence(1,"{");
	write_sentence(2,"flag_token=1;");
	write_sentence(2,"nowken=get_token();");
	write_sentence(1,"}");
	write_sentence(1,"return nowken;");
	write_sentence(0,"}");
	write_sentence(0,"int main()");
	write_sentence(0,"{");
	write_sentence(1,"DFA__init();");
	write_sentence(1,"char* file_name=;//�˴���Ҫ���ļ���");
	write_sentence(1,"flag_token=0;");
	write_sentence(1,"freopen(file_name,\"r\",stdin);");
	write_sentence(1,"DFA__state=DFA__from;");
	write_sentence(0,"}");
} 
