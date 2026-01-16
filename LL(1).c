#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#define MAX_STACK 100
#define MAX_LINE 100
#define MAX_PROD 20
#define MAX_VN 10
#define MAX_VT 10
#define MAX_QUAT 10
//LL(1) 
char VN[MAX_VN][10]={"E","E1","T","T1","F"};//非终结符
int vn_count=5;
char VT[MAX_VT][10]={"i","w1","w2","(",")","#"};//终结符
int vt_count=6;
char quat[MAX_QUAT][50];//存储四元式 
int quat_count = 0;
//转换表 
int table[MAX_VN][MAX_VT] = {
    {1, 0, 0, 1, 0, 0},
    {0, 2, 0, 0, 3, 3},
    {4, 0, 0, 4, 0, 0},
    {0, 6, 5, 0, 6, 6},
    {7, 0, 0, 8, 0, 0}
};
//属性翻译文法 
char production[MAX_PROD][5][10] = {
    {"T", "E1"},
    {"w1", "T", "GEQ", "E1"},
    {"&"},
    {"F", "T1"},
    {"w2", "F", "GEQ", "T1"},
    {"&"},
    {"i"},
    {"(", "E", ")"}
};
//存放单词 
char sem[MAX_STACK][10];
int sem_top=0;
int sem_end=0; 
//存放分析过程 
char syn[MAX_STACK][10];
int syn_top=0;
int syn_end=0; 
//存储要进行语法语义分析的算术表达式
char words[MAX_STACK][10];
int word_top=0;
int word_end=0;

//接收终结符/非终结符/运算符 
char word[10];
char symbol_var[10];

//存放运算符 
char symbol[MAX_STACK][10];
int s_top=0;
int s_end=0; 
//临时变量命名相关
int counter=1; 


//从要分析的算术表达式中取单词 
char *get_w(){
	//没有要进行分析的 句子 
	if(word_top<=0){
		return NULL;
	}
	char *w=words[word_end];
	word_end++;//指针右移
//	printf("%s",w); 
	return w; 
}
void push_word(char *w){
	strcpy(words[word_top],w);
	word_top++;
}

char *pop_symbol(){
	if (s_top<=0){
		return '\0';
	}
	s_top--;
	char *s=symbol[s_top];
	return s;
}
void push_symbol(char *s){
	strcpy(symbol[s_top],s);
	s_top++;
}

char* pop_syn(){
	if(syn_top<=0){
		return '\0';
	}
	syn_top--;
	char *s=syn[syn_top];
	return s;
}
void push_syn(char *s){
	strcpy(syn[syn_top],s);
	syn_top++;
}
char* pop_sem(){
	if(sem_top<=0){
		return '\0';
	}
	sem_top--;
	char *s=sem[sem_top];
	return s;
}
void push_sem(char *s){
	strcpy(sem[sem_top],s);
	sem_top++;
}
int getVNIndex(char *s){
	int i;
	for (i=0;i<vn_count;i++){
		if(!strcmp(s,VN[i])){
			return i;
		}
	}
	return -1;
}
//找到终结符相对位置 并进行转换 
int getVTIndex(char *w){
	int i;
	char *modify;
	if(isalnum(w[0]) || (isalpha(w[0]) && islower(w[0]))){
		strcpy(modify,"i"); 
	}else if (strcmp(w,"+")==0 || strcmp(w,"-")==0){
		strcpy(modify,"w1");
	}else if (strcmp(w,"*")==0 || strcmp(w,"/")==0){
		strcpy(modify,"w2");
	}else if(strcmp(w,"#")==0){
		strcpy(modify,"#");
	}else if(strcmp(w,")")==0){
		strcpy(modify,")");
	}else if(strcmp(w,"(")==0){
		strcpy(modify,"(");
	}else {
		printf("出错，该字符无法识别！");
		return -1;
	}
	for (i=0;i<vt_count;i++){
		if(!strcmp(modify,VT[i])){
			return i;
		}
	}
	return -1;
}
//初始存要分析的算术表达式 
void initWords(char *str) {
    int i;
    int len = strlen(str);  //使用 strlen
    
    for (i = 0; i < len; i++) {
        char temp[2] = {str[i], '\0'};  // 将字符转为字符串
        printf("压栈word:%s\n",temp);
        push_word(temp);  //传递字符串
    }
}
// 生成临时变量
char* newTemp() {
    static char temp[10];
    sprintf(temp, "T%d", counter++);
    return temp;
}
// 生成四元式
void GEQ() {
    char* right = pop_sem();
    char* op = pop_symbol();
    char* left = pop_sem();
    char* temp = newTemp();
    sprintf(quat[quat_count], "(%s, %s, %s, %s)", op, left, right, temp);
    quat_count++;
    
    push_sem(temp);		//将生成的临时变量推入语义栈 
}

//非终结符处理 查询分析表 
bool getNonTerminalIndex(){
	int vn_idx=getVNIndex(symbol_var);
	int vt_idx=getVTIndex(word);
	int prod=table[vn_idx][vt_idx]-1;
	if(prod==-1){
		printf("状态转换出错:");
		return false;
	}
	//逆序压栈
	int len=0;
	while(len<5 && strlen(production[prod][len])>0){
		len++;
	} 
	int i;
	for(i=len-1;i>=0;i--){
		printf("=============逆序压栈算式：%s\n",production[prod][i]); 
		if(strcmp(production[prod][i], "&") != 0){
			push_syn(production[prod][i]);
		}
	}
	printf("\n");
	return true;
}
//终结符的处理 比较是否和算术式中的符号相同 
bool getTerminalIndex(){
	if (strcmp(symbol_var,"i")==0){
		if(!isdigit(word[0]) && (isalpha(word[0]) && !islower(word[0]))){
			printf("单词出错!\n");
			return false;
		}else{
			push_sem(word);//单词压栈 
		}
	}
	if( strcmp(symbol_var,"w1")==0 ){
		if(strcmp(word,"+")!=0 &&  strcmp(word,"-")!=0 ){
			printf("w1出错\n");
			return false;
		}else{
			push_symbol(word);//符号压栈符号栈 
		}
	}
	if( strcmp(symbol_var,"w2")==0 ){
		if(strcmp(word,"*")!=0 && strcmp(word,"/")!=0 ){
			printf("w2出错\n");
			return false;
		}else{
			push_symbol(word);//符号压栈符号栈 
		}
	}
	if(strcmp(symbol_var,"(")==0){
		if(strcmp(word,"(")!=0){
			printf("括号缺失\n");
			return false;
		}
	}
	if(strcmp(symbol_var,")")==0){
		if(strcmp(word,")")!=0){
			printf("括号缺失\n");
			return false;
		}
	}
	if (word_end==word_top){
		printf("单词栈已空，未找到终止符");
		return false;
	}
	strcpy(word,get_w());
	return true;
}
void LL_Analysis(char *str){
	initWords(str);
	// 开始符号压栈 
	push_syn("#");
	push_syn("E");
	char *temp = get_w();
	//取出要分析的算术式中的字符 
	strcpy(word, temp);
	//取出分析栈中字符 
	strcpy(symbol_var,pop_syn());
	while(strcmp(symbol_var,"#")!=0){
        // 打印当前状态
        printf("当前symbol_var:%s ", symbol_var);
        printf("当前word:%s\n", word);
		
		if(strcmp(symbol_var,"GEQ")==0){
			GEQ();
		}else if (strcmp(symbol_var,"i")==0 || strcmp(symbol_var,"w1")==0 || strcmp(symbol_var,"w2")==0 || strcmp(symbol_var,"(")==0 || strcmp(symbol_var,")")==0){
			if(!getTerminalIndex()){
				return;
			}
		}else if(strcmp(symbol_var,"E")==0 || strcmp(symbol_var,"E1")==0 || strcmp(symbol_var,"T")==0 || strcmp(symbol_var,"T1")==0 || strcmp(symbol_var,"F")==0){
			if(!getNonTerminalIndex()){
				return;
			}
		}
		strcpy(symbol_var,pop_syn());		
			
	}
	printf("\n四元式:\n");
	int i;
    for(i = 0; i < quat_count; i++) {
        printf("%s\n", quat[i]);
    }
	
}
void readFile(char *fileName) {
    FILE *fp = fopen(fileName, "r");
    if (fp == NULL) {
        printf("文件打开失败或文件为空\n");
        return;
    }

    char line[MAX_LINE];
    if (fgets(line, MAX_LINE, fp) != NULL) {  // 只读一行
        // 去除换行符
        
        line[strcspn(line, "\n")] = 0;
        printf("读取的要转换的算术表达式：%s",line);
    } else {
        printf("文件为空或读取失败\n");
        fclose(fp);
        return;
    }

    fclose(fp);
    // 开始分析
    LL_Analysis(line);
}	
	
	
int main(){
	readFile("exa2.txt");
}

























