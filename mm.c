// 들어가기전에. 정글 & CMU에서 얘기하는 팁
// csapp 9.9장을 참고할 것
// make시에 아래와 같은 인자를 추가로 사용할 수 있다
//  -v, V : 각 trace 파일에 대한 요약을 확인할 수 있음
//  -f : 특정 트레이스 파일만 디버깅 용으로 집어넣어볼 수 있다. short1-bal.rep, short2-bal.rep 사용해볼 것
// 디버거, 프로파일러 사용도 추천한다. gcc기준으로 컴파일할 때 -g, -pg 인자 사용
// 일단 박고봐라!

// 왜 포인터 참조를 통한 할당과 매크로를 통한 할당이 값이 차이가 나는가.............. 왜...........왜.......


#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

// word, double word의 사이즈를 정의한다. 정렬기준은 64비트 체제에 맞춰 8바이트 = dw. 이거 w/dw 사이즈 매우 헷갈리는데 일단 그냥 받아들이기로 한다.
#define WSIZE 4
#define DSIZE 8
#define ALIGNMENT DSIZE
// 사이즈를 8의 배수로 올림하는 작업. dw기준 7을 더한 후 하위 3개비트는 모두 버린다
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
// size_t 타입을 8바이트 정렬 처리한다. 사용하는 체제에 따라 size_t의 크기가 다를 수 있는데, 플랫폼에 독립적인 코드를 위한 처리라고 생각하겠음.
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
// 힙의 확장단위(4096바이트)를 정의한다
#define HEAP_CHUNK_SIZE (1<<12)
// 맥스값을 찾는 매크로를 정의한다. ?a:b는 true일때 a, false일때 b를 반환한다고함. 괄호를 사용하면 서순에 맞게 연산이 안전하게 이루어진다는것도 염두해두면 좋음.
#define MAX(x, y) ((x) > (y) ? (x) : (y))
// size에 alloc(0,1)을 패키징하는 단순한 매크로. size의 최하위 비트가 0이라는 전제가 필요하다.
#define PACK(size, alloc) ((size) | (alloc))
// 포인터를 통해 값을 가져오거나 할당하는 매크로. 포인터를 uint로 형변환 하고 있는거만 체크해두자.
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = val)
// 헤더(또는 풋터)의 포인터를 통해 블록의 사이즈와 할당정보를 알 수 있는 단순한 매크로
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
// 메모리블록의 포인터 bp를 통해 헤더, 풋터의 포인터를 찾는 매크로
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE((char*)(bp) - WSIZE) - DSIZE)
// 다음, 이전 bp를 찾는 매크로를 지정한다. 각각 헤더와 풋터에 있는 사이즈 정보를 이용하는것.
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE((char*)(bp) - WSIZE))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE((char*)(bp) - DSIZE))

// 추가로 필요한 함수를 정의한다
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
void *first_fit(size_t alloc_size);

// 추가로 필요한 변수를 정의한다

static void *extend_heap(size_t words){
    char *bp;
    size_t size;
    // 받은 words를 토대로, size를 8바이트의 배수로 복원하고 그 크기만큼 할당한다
    // ex. 12바이트를 요청받은 경우 >> 16바이트로 사이즈를 복원하고 할당
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    printf("확장 사이즈는 : %i\n", size);
    // 포인터와 정수를 비교하기 위해 void*을 long으로 캐스팅한다. windows는 long long 써야할듯?
    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL; 
    }
    // 힙을 확장한 후 해당 블록의 헤더, 풋터의 정보들을 갱신한다
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), 1); // 새로운 에필로그 헤더가 된다
    // 이전 블록이 열려있으면 연결한 후 bp를 반환한다
    return coalesce(bp);
}

static void *coalesce(void *bp){
    // 앞 블록이 사용 가능하면 병합한다
    char* bp_prev = PREV_BLKP(bp);
    if (!GET_ALLOC(HDRP(bp_prev))){
        size_t new_size = GET_SIZE(HDRP(bp_prev)) + GET_SIZE(HDRP(bp));
        printf("sizebp:%i, sizeprevbp:%i, new_size:%i\n", GET_SIZE(HDRP(bp)), GET_SIZE(HDRP(bp_prev)),new_size);
        PUT(HDRP(bp_prev), PACK(new_size, 0));
        bp = bp_prev; // ptr을 이전 블록까지 땡겨놓는다. 뒤에 if문 걸릴때 블록 병합에 대비 + 리턴 대비
        printf("ftrp : %p, hdrp : %p", FTRP(bp), HDRP(bp));
        PUT(FTRP(bp), *HDRP(bp)); // 풋터 갱신
    }
    char* bp_next = NEXT_BLKP(bp);
    // 뒷 블록이 사용 가능하면 병합한다
    if (!GET_ALLOC(HDRP(bp_next))){
        PUT(HDRP(bp), GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(bp_next)));
        PUT(FTRP(bp), *HDRP(bp)); // 풋터 갱신
    }
    return bp;
}


// 힙에 사전에 정의된 크기의 메모리를 할당하고 초기화한다
int mm_init(void)
{
    // 힙을 생성하고 초기 포인터를 반환받는다. 실패시 에러 메세지를 받는다.
    char* heap_listp = mem_sbrk(4*WSIZE);
    if (heap_listp == (void*)-1){
        return -1;
    }
    // 처음 힙을 생성할 때, 필요한 작업을 한다
    PUT(heap_listp + WSIZE*0, 0); // 첫번째 워드는 정렬을 맞추기 위해 0을 박는다
    PUT(heap_listp + WSIZE*1, PACK(DSIZE, 1)); // 두번째 워드는 프롤로그 헤더. 사이즈 + 할당정보 
    PUT(heap_listp + WSIZE*2, PACK(DSIZE, 1)); // 세번째 워드는 프롤로그 풋터. 사이즈 + 할당정보
    PUT(heap_listp + WSIZE*3, 1); // 네번째 워드는 에필로그 헤더. 사이즈는 0이고 할당정보만 넣는다

    // 힙을 확장
    if (extend_heap(HEAP_CHUNK_SIZE/WSIZE) == NULL){
        return -1;
    }
    return 0;
}

// first-fit 방식의 할당을 구현한다. 비어있는 bp를 반환한다
void *first_fit(size_t alloc_size){
    // 힙 시작점을 받아온다
    char *bp = mem_heap_lo() + 16; // 패딩 4바이트, 프롤로그 8바이트, 헤더 4바이트 .. 시작점에서 16바이트 뒤에 첫 bp가 있다
    while(GET_SIZE(HDRP(bp)) != 0){
        printf("현재포인터 : %p, size : %i, alloc : %i\n", bp, GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)));
        // 할당되어있지않고, 사이즈가 충분한 경우
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= alloc_size){
            printf("찾았습니다!\n");
            return bp;
        }
        // 조건을 만족하지 못하면 다음 블록으로 넘어간다
        bp = NEXT_BLKP(bp);
    }
    // 못찾았으면 void*(-1)을 반환한다
    printf("firstfit 실패!\n");
    return (void*)-1;
}


// 메모리를 할당하고 포인터를 반환한다
void *mm_malloc(size_t size){
    // 헤더+풋터(=8바이트)를 포함해서 필요한 사이즈를 정의한다
    int new_size = ALIGN(size + SIZE_T_SIZE);
    printf("\n필요한 사이즈 : %i\n", new_size);
    
    // first fit : 힙의 처음부터 끝까지 스프린트 하면서 가능한 공간을 찾는다
    printf("스프린트 시작\n");
    char *bp = first_fit(new_size);
    // 가용 메모리가 부족하면 힙을 확장한다
    if (bp == (void*)-1){
        printf("힙을 확장합니다!\n\n");
        bp = extend_heap(new_size/WSIZE); // 여기 확장하는 사이즈 나중에 다시 볼것!
    }
    // bp를 기준으로 할당처리를한다
    size_t remain_size = GET_SIZE(HDRP(bp)) - new_size; // 여기 데이터 타입이 size_t가 맞을까..?
    // 헤더, 풋터에 할당, 사이즈 정보를 넣는다
    PUT(HDRP(bp), PACK(new_size, 1));
    PUT(FTRP(bp), PACK(new_size, 1));
    // 남는 블록이 16바이트이상(헤더,풋터 포함 데이터를 가질 수 있는 최소값)이면 헤더, 풋터에 할당, 사이즈 정보를 넣는다
    if (remain_size >= 16){
        void *bp_next = NEXT_BLKP(bp);
        PUT(HDRP(bp_next), PACK(remain_size, 0));
        PUT(FTRP(bp_next), PACK(remain_size, 0));
    }
    // 포인터를 반환한다
    return bp;
}

// 해당 블록을 해제하고, 앞 뒤 블록이 할당되지 않은 상태면 병합한다
void mm_free(void *bp){
    // 할당되지 않은 상태면 에러를 반환한다
    if (!GET_ALLOC(HDRP(bp))){
        exit(EXIT_FAILURE);
    }
    printf("\n해제합니다!!\n");
    printf("bp : %p, size : %i\n", bp, GET_SIZE(HDRP(bp)));
    // 할당된 상태면 할당정보인 1을 헤더, 풋터에서 제거해준다
    PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 0));
    PUT(FTRP(bp), PACK(GET_SIZE(FTRP(bp)), 0));

    // 앞뒤 블록을 병합한다
    coalesce(bp);
    printf("해제 및 병합 완료\n");
    return;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














