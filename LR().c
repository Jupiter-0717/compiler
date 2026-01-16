#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdbool.h>

#define MAX_STACK 100
#define MAX_LINE 256
#define MAX_QUAT 100
#define MAX_STATES 50
#define MAX_SYMBOLS 20

//LR(0)
char current_input[10];
//存放终结符 
char sem[MAX_STACK][10];
int sem_top = 0;

//分析栈（用于LR分析）
char syn[MAX_STACK][10];
int syn_top = 0;

//状态栈
int state_stack[MAX_STACK];
int state_top = 0;

//输入串
char words[MAX_STACK][10];
int word_top = 0;
int word_end = 0;

//四元式
char quat[MAX_QUAT][50];
int quat_count = 0;

//临时变量计数器
int counter = 1;

// 产生式定义
typedef struct {
    char left[10];      // 产生式左部
    char right[5][10];  // 产生式右部
    int length;         // 右部长度，规约依据 
} Production;

// 定义产生式
Production productions[] = {
    {"E'", {"E"}, 1},                 // 0: E' -> E
    {"E", {"E", "w1", "T","GEQ"}, 4}, // 1: E -> E + T
    {"E", {"T"}, 1},                  // 2: E -> T
    {"T", {"T", "w2", "F","GEQ"}, 4}, // 3: T -> T * F
    {"T", {"F"}, 1},                  // 4: T -> F
    {"F", {"(", "E", ")"}, 3},        // 5: F -> (E)
    {"F", {"i","PUSH"}, 2}            // 6: F -> i
};
int prod_count = 7;

// ACTION表：[状态][终结符] -> 动作
// s表示移进，r表示规约，acc表示接受
// 格式："s5"表示移进到状态5，"r2"表示用产生式2规约
char ACTION[MAX_STATES][10][10];

// GOTO表：[状态][非终结符] -> 状态
int GOTO[MAX_STATES][10];

// 终结符和非终结符
char terminals[][10] = {"i", "w1", "w2", "(", ")", "#"};
int terminal_count = 6;

char non_terminals[][10] = {"E'", "E", "T", "F"};
int non_terminal_count = 4;

// 初始化LR(0)分析表（需要根据文法构造）
void initLRTable() {
    // 状态0
    GOTO[0][3] = 7;
    strcpy(ACTION[0][0], "s8");  
    strcpy(ACTION[0][3], "s9");  
    GOTO[0][1] = 1;  
    GOTO[0][2] = 4;  

    // 状态1
    strcpy(ACTION[1][1], "s2"); 
    strcpy(ACTION[1][5], "acc");  
    // 状态2
    strcpy(ACTION[2][0], "s8");  
    strcpy(ACTION[2][3], "s9");  
    GOTO[2][2] = 3;  
    GOTO[2][3] = 7;  
    // 状态3
    strcpy(ACTION[3][1], "r1");  
    strcpy(ACTION[3][2], "s5"); 
	strcpy(ACTION[3][4], "r1");  
	strcpy(ACTION[3][5], "r1");   
	// 状态4
    strcpy(ACTION[4][1], "r2");  
    strcpy(ACTION[4][2], "s5"); 
	strcpy(ACTION[4][4], "r2");  
	strcpy(ACTION[4][5], "r2"); 	 
    // 状态5
    strcpy(ACTION[5][0], "s8");  
    strcpy(ACTION[5][3], "s9"); 
	GOTO[5][3] = 6;  
	// 状态6
    strcpy(ACTION[6][0], "r3");  
    strcpy(ACTION[6][1], "r3"); 
	strcpy(ACTION[6][2], "r3");  
	strcpy(ACTION[6][3], "r3");	 
	strcpy(ACTION[6][4], "r3");	
    strcpy(ACTION[6][5], "r3");	
    // 状态7
    strcpy(ACTION[7][0], "r4");  
    strcpy(ACTION[7][1], "r4"); 
	strcpy(ACTION[7][2], "r4");  
	strcpy(ACTION[7][3], "r4");	 
	strcpy(ACTION[7][4], "r4");	
    strcpy(ACTION[7][5], "r4");	
    // 状态8
    strcpy(ACTION[8][0], "r6");  
    strcpy(ACTION[8][1], "r6"); 
	strcpy(ACTION[8][2], "r6");  
	strcpy(ACTION[8][3], "r6");	 
	strcpy(ACTION[8][4], "r6");	
    strcpy(ACTION[8][5], "r6");	
    // 状态9
    strcpy(ACTION[9][0], "s8");  
    strcpy(ACTION[9][3], "s9");  
    GOTO[9][1] = 10;  
    GOTO[9][2] = 4;  
    GOTO[9][3] = 7;  
    // 状态10
    strcpy(ACTION[10][1], "s2");  
    strcpy(ACTION[10][4], "s11");  
    // 状态11
    strcpy(ACTION[11][0], "r5");  
    strcpy(ACTION[11][1], "r5"); 
	strcpy(ACTION[11][2], "r5");  
	strcpy(ACTION[11][3], "r5");	 
	strcpy(ACTION[11][4], "r5");	
    strcpy(ACTION[11][5], "r5");	
}

// 获取终结符索引
int getTerminalIndex(char *s) {
    // 处理标识符和运算符
    char modify[10];
//    printf("s[0]:%c\n",s[0]);
    if (isdigit(s[0]) || (isalpha(s[0]) && islower(s[0]))) {
        strcpy(modify, "i");
    } else if (strcmp(s, "+") == 0 || strcmp(s, "-") == 0) {
        strcpy(modify, "w1");
    } else if (strcmp(s, "*") == 0 || strcmp(s, "/") == 0) {
        strcpy(modify, "w2");
    } else {
        strcpy(modify, s);
    }
    int i;
    for (i = 0; i < terminal_count; i++) {
        if (strcmp(modify, terminals[i]) == 0) {
            return i;
        }
    }
    return -1;
}

// 获取非终结符索引
int getNonTerminalIndex(char *s) {
	int i;
    for (i = 0; i < non_terminal_count; i++) {
        if (strcmp(s, non_terminals[i]) == 0) {
            return i;
        }
    }
    return -1;
}

// 语义栈操作
void push_sem(char *s) {
    strcpy(sem[sem_top++], s);
}

char* pop_sem() {
    if (sem_top > 0) {
        return sem[--sem_top];
    }
    return NULL;
}

// 符号栈操作
void push_syn(char *s) {
    strcpy(syn[syn_top++], s);
}

char* pop_syn() {
    if (syn_top > 0) {
//    	printf("符号栈栈顶%s\n",syn[syn_top]);
        return syn[--syn_top];
    }
    return NULL;
}

// 状态栈操作
void push_state(int s) {
    state_stack[state_top++] = s;
}

int pop_state() {
    if (state_top > 0) {
        return state_stack[--state_top];
    }
    return -1;
}
// 取栈顶  
int top_state() {
    if (state_top > 0) {
        return state_stack[state_top - 1];
    }
    return -1;
}


// 生成临时变量
char* newTemp() {
    static char temp[10];
    sprintf(temp, "T%d", counter++);
    return temp;
}

// 语义动作：生成四元式
void generateQuaternion(int len) { 
    char *right = pop_sem();
	int i;
	char *op;
	printf("len:%d\n",len);
	for (i = 0; i < len; i++){
		char *o = pop_syn();
		if (strcmp(o, "+") == 0 || strcmp(o, "-") == 0 ||strcmp(o, "*") == 0 || strcmp(o, "/") == 0){
			op = o;
		}
	}
    char *left = pop_sem();
    char *temp = newTemp();
    sprintf(quat[quat_count++], "(%s, %s, %s, %s)", op, left, right, temp);
    push_sem(temp);
    
}

// 初始化输入串
void initWords(char *str) {
    int i = 0, j = 0;
    word_top = 0;
    
    while (str[i] != '\0') {
        if (str[i] == ' ') {
            i++;
            continue;
        }
        j = 0;
        if (isalnum(str[i]) || isalpha(str[i])) {
        	// 接口 
            while (isalnum(str[i]) || isalpha(str[i])) {
                words[word_top][j++] = str[i++];
            }
        } else {
            words[word_top][j++] = str[i++];
        }
        words[word_top][j] = '\0';
        word_top++;
        
    }
    
    // 添加结束符 自己加也行 
//    strcpy(words[word_top++], "#");
}

// LR(0)语法分析主函数
bool LR_Analysis() {
    initLRTable();
    // 初始化：状态0入栈
    push_state(0);
    
    int input_index = word_end;
    strcpy(current_input,words[input_index]);
    printf("\n开始LR()语法分析...\n");
    printf("%-10s %-30s %-30s %-20s\n", "步骤", "状态栈", "符号栈", "输入串");
    printf("------------------------------------------------------------------------------------\n");
    int step = 0;
    while (true) {
        step++;
        //当前状态 
        int current_state = top_state();
        //当前w 
        int term_idx = getTerminalIndex(current_input);
        // 错误处理 
        if (term_idx == -1) {
            printf("错误：无法识别的符号 %s\n", current_input);
            return false;
        }
        //当前动作 
        char *action = ACTION[current_state][term_idx];
        
        // 打印当前状态栈、符号栈及剩余输入串信息 
        printf("%-10d ", step);
        int i;
        for (i = 0; i < state_top; i++) printf("%d ", state_stack[i]);
        printf("%-30s", "");
        for (i = 0; i < syn_top; i++) printf("%s ", syn[i]);
        printf("%-30s", "");
        for (i = input_index; i < word_top; i++) printf("%s", words[i]);
        printf("\n");
        
        if (action[0] == 's') {  //移进
            int next_state = atoi(&action[1]);
            push_state(next_state);
            push_syn(current_input);
            
            input_index++;
            strcpy(current_input,words[input_index]);

        } else if (action[0] == 'r') {  
		//规约
            int prod_num = atoi(&action[1]);
            Production prod = productions[prod_num];
            
            printf("规约：%s -> ", prod.left);
            int i;
            for (i = 0; i < prod.length; i++) {
                printf("%s ", prod.right[i]);
            }
            printf("\n");
            int len = prod.length;
            // 弹出相应数量的状态和符号
            if (strcmp(prod.right[i-1],"GEQ") == 0){
            	// 执行语义动作
            	len--;
            	generateQuaternion(len);
				            	
			}
			if (strcmp(prod.right[i-1],"PUSH") == 0){
				char *w = pop_syn();
    			push_sem(w);
    			len--;
			}
            
            for (i = 0; i < len; i++) {
                pop_state();
				// 只有在没有PUSH和GEQ的情况下才弹符号栈
			    if (strcmp(prod.right[prod.length-1], "PUSH") != 0 && strcmp(prod.right[prod.length-1], "GEQ") != 0) {
			        pop_syn();
			    }

            }
            // 查GOTO表
            int goto_state = top_state();
            int non_term_idx = getNonTerminalIndex(prod.left);
            int next_state = GOTO[goto_state][non_term_idx];
            push_state(next_state);
            push_syn(prod.left);
            
        } else if (strcmp(action, "acc") == 0) {  // 接受
            printf("\n语法分析成功！\n");
            return true;
        } else { // 错误处理 生成详细的报错信息 便于调试 
            printf("错误：在状态%d遇到符号%s时无法继续\n", current_state, current_input);
            return false;
        }
    }
}

// 读取文件
void readFile(char *fileName) {
    FILE *fp = fopen(fileName, "r");
    if (fp == NULL) {
        printf("打开文件失败\n");
        return;
    }
    
    char line[MAX_LINE];
    if (fgets(line, MAX_LINE, fp) != NULL) {
        line[strcspn(line, "\n")] = 0;
        printf("读取表达式：%s\n", line);
        initWords(line);
        
        if (LR_Analysis()) {
            printf("\n生成的四元式：\n");
            int i;
            for (i = 0; i < quat_count; i++) {
                printf("%d: %s\n", i + 1, quat[i]);
            }
        }
    }
    
    fclose(fp);
}

int main() {
    readFile("exa2.txt");
    return 0;
}
