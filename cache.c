#include "cachelab.h"
#include "stdlib.h"
#include <stdio.h>
#include "getopt.h"
#include <string.h>


int S, E, B;
int miss, hit, eviction;

typedef struct _Node {
    unsigned tag;
    struct _Node* next;
    struct _Node* prev;
}Node;

typedef struct _LRU {
    int *size;
    Node* head;
    Node* tail;
}LRU;

LRU* lru;

// 初始化lru
void init_LRU(int id) {
    (lru[id].size) = (int *) malloc(sizeof(int));
    *(lru[id].size) = 0;
    lru[id].head = (Node *) malloc(sizeof(Node));
    lru[id].tail = (Node *) malloc(sizeof(Node));
    lru[id].head->next = lru[id].tail;
    lru[id].tail->prev = lru[id].head;
}

// 删除curLru中node节点的元素
void deleteElement(Node *node, LRU *curLru) {
    node->prev->next = node->next;
    node->next->prev = node->prev;
    *(curLru->size) = *(curLru->size) - 1;
}

// 在双向链表头部加入元素
void addElement(Node *node, LRU *curLru) {
    node->next = curLru->head->next;
    node->prev = curLru->head;
    curLru->head->next->prev = node;
    curLru->head->next = node;
    *(curLru->size) = *(curLru->size) + 1;
}

void readOption(int argc, char **argv, char** fileName) {
    int option;
    while ( (option = getopt(argc, argv, "s:E:b:t:")) != -1) {
        if (option == 's') S = atoi(optarg);
        if (option == 'E') E = atoi(optarg);
        if (option == 'b') B = atoi(optarg);
        if (option == 't') strcpy(*fileName, optarg);
    }
}

void update (int address) {
    unsigned targetTag = address >> (S + B); // 标记
    unsigned targetSet = (address >> B) & (0xFFFFFFFF >> (32 - S));

    LRU curLRU = lru[targetSet];

    Node* cur = curLRU.head->next;
    unsigned isfound = 0;
    while (cur != curLRU.tail) {
        if (cur->tag == targetTag) {
            isfound = 1;
            break;
        }
        cur = cur->next;
    }

    if (isfound) {
        hit ++; // 命中
        deleteElement(cur, &curLRU);
        addElement(cur, &curLRU);
        printf("hit ");
    } else {
        Node* newNode = (Node *)malloc(sizeof(Node));
        newNode->tag = targetTag;
        printf("miss ");
        if (*(curLRU.size) == E) {
            eviction ++;
            deleteElement(curLRU.tail->prev, &curLRU);
            addElement(newNode, &curLRU);
            printf("eviction ");
        } else {
            addElement(newNode, &curLRU);
        }
        miss++;
    }
}

void cacheRun(char* fileName) {
    // 初始化lru
    lru = (LRU *)malloc((1 << S) * sizeof(*lru));
    for (int i = 0; i < (1 << S); i ++) init_LRU(i);

    FILE *file = fopen(fileName, "r");
    char op;
    unsigned address;
    int size;
    while (fscanf(file, " %c %x,%d", &op, &address, &size) > 0) {
        printf("%c %x,%d ", op, address, size);
        if (op == 'L') update(address);
        else if (op == 'S') update(address);
        else if (op == 'M') update(address), update(address);
        printf("\n");
}
}
int main(int argc, char **argv)
{
    char* fileName = (char *)malloc(100 * sizeof(char));
    
    readOption(argc, argv, &fileName);

    cacheRun(fileName);

    printSummary(hit, miss, eviction);
    return 0;
}
