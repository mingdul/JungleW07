/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
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
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) //어떤 사이즈가 들어오든 가장 가까운 8의 배수 올려줌

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) 

#define WSIZE 4
#define DSIZE 8
#define CHUNCKSIZE (1<<12) //동적 메모리 할당기에서 힙을 한 번에 늘리는 기본 단위 크기
//heap 영역을 CHUNKSIZE 만큼 늘려줌
//대부분의 운영체제에서 페이지 크기가 4KB(4096)

#define MAX(x,y)((x)>(y)?(x):(y))

#define PACK(size, alloc) ((size)|(alloc)) //사이즈랑 할당 정보를 하나의 4바이트(8바이트)) 워드에 저장
//size와 alloc을 or연산하면 사이즈는 그대로 유지, 마지막 비트에 할당여부만 들어감

//read and write a word at address p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p,val) (*(unsigned int *)(p)=(val))

#define GET_SIZE(p) (GET(p)& ~0x7)
#define GET_ALLOC(p) (GET(p)&0x1)

#define HDRP(bp) ((char *)(bp)-WSIZE) // 블록포인터로 해더주소 계산, 형변환: 포인터 연산을 바이트 단위로 하려고
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 
//#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp) - DSIZE)) // HDRP(bp)가 아닌 HDRP(bp - DSIZE)처럼해석

//GET_SIZE(HDRP(bp)-DSIZE) : 전체 블록에서 8바이트(해더+푸터)를 빼면 payload+padding 영역 길이 나옴
//bp에서 GET_SIZE(HDRP(bp)-DSIZE)더하면 푸터 주소나옴

// #define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) -WSIZE)))
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))  
// GET_SIZE: 해더에 저장된 블록의 사이즈를 읽음
#define PREV_BLKP(bp) ((char*)(bp)-GET_SIZE(((char*)(bp)-DSIZE)))


static void *extend_heap(size_t words);
int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);
static void *find_fit(size_t asize);
static void place(void *bp,size_t asize);
static void *coalesce(void *bp);

static char *heap_listp=0;


//extend heap/////////////////////////////////////////////////////////////////////////////////
/*
 * mm_init - initialize the malloc package.
 creates a heap with an initial free block
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp=mem_sbrk(4*WSIZE))==(void*)-1)
        return -1;

    PUT(heap_listp,0); //정렬패딩
    PUT(heap_listp+(1*WSIZE),PACK(DSIZE,1)); //prologue header
    PUT(heap_listp+(2*WSIZE),PACK(DSIZE,1)); //prologe footer
    PUT(heap_listp+(3*WSIZE),PACK(0,1)); //epilogue header
    heap_listp +=(2*WSIZE);

    //extend the empty heap with a free block of 청크사이즈 바이트
    if (extend_heap(CHUNCKSIZE/WSIZE) ==NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    //allocate even number of words to maintain alignment
    size=(words%2)?(words+1)*WSIZE:words*WSIZE;
    if ((long)(bp=mem_sbrk(size))==-1) 
        return NULL;
    //mem_sbrk(size): 힙영역을 사이즈 만큼 늘려달라고 요청하는 함수 실패하면 -1을 리턴한다
    //bp=새로얻은 힙 메모리 블록의 시작 주소 예외처리인데 바꿔주긴함
    //포인터랑 비교해야하니까 롱타입

    //initailize free block header/footer and epilogue header
    PUT(HDRP(bp),PACK(size,0)); // freeblock header
    PUT(FTRP(bp),PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1)); //new epiloge header

    return coalesce(bp); //coalesce if the previous block was free


}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    
    size_t asize; //조정된 블록 크기(정렬+ 해더/풋터)
    size_t extendsize; //힙을 얼마나 늘려야할지 저장
    char *bp; //블록 포인터

    if (size==0){
        return NULL;
    }

    if (size<=DSIZE)
        asize=2*DSIZE; //헤더(4B) + 풋터(4B) + 최소 payload(8B) = 16B
    else
        asize=DSIZE*((size+(DSIZE)+(DSIZE-1)) / DSIZE);

    if ((bp=find_fit(asize)) !=NULL){ //find_fit(asize): 크기가 asize이상인 빈공간을 찾는다 
        place(bp,asize); //찾으면 그 블록을 할당표시하고 나눔
        return bp;
    }

    //빈블록이 없다면 힙을 확장
    extendsize=MAX(asize,CHUNCKSIZE); //확장크기는 요청크기와 청크사이즈중 큰걸로 함 
    if ((bp=extend_heap(extendsize/WSIZE)) ==NULL){
        return NULL;
    }
    place(bp,asize); //새로 확장한 곳에 요청한 크기만큼 블록을 배치
    return bp;

    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
    //     return NULL;
    // else
    // {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) //bp: 할당 해제할 블록의 포인터
{
    size_t size=GET_SIZE(HDRP(bp)); //지금 블록의 크기 가져오기

    PUT(HDRP(bp), PACK(size,0)); //해더와 풋터를 0 표시로 덮여 씌운다
    PUT(FTRP(bp), PACK(size,0));
    coalesce(bp); //인접 가용블록들과 합칠수 있음 합침

}

static void *coalesce(void *bp)
{
    size_t prev_alloc= GET_ALLOC(FTRP(PREV_BLKP(bp))); //이전 블록이 할당되어있는지 확인
    size_t next_alloc=GET_ALLOC(HDRP(NEXT_BLKP(bp))); //다음 블록이 할당되어있는지 확인
    size_t size=GET_SIZE(HDRP(bp)); //현재 블록의 크기

    if (prev_alloc && next_alloc){ //케이스1 양옆모두 할당 : 그대로
        return bp;
    } 

    else if (prev_alloc&&!next_alloc){ //case2 : 다음 블록이랑 합침 //둘이 모두 참이어야 조건문이 실행된다
        size+=GET_SIZE(HDRP(NEXT_BLKP(bp))); //현재 블록 크기에 다음 블록 크기를 더함
        //새로운 크기내 해더와 풋터
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }
    else if (!prev_alloc&&next_alloc){
        size+=GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0)); //해더는 항상 블록의 시작에 있으니까 이전 블록 해더에 새 크기를 기록해야함
        
        bp=PREV_BLKP(bp); //합쳐진 새 블록의 시작은 이전블록
    }
    else{
        size+=GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0)); 
        //case2에서는 현재와 다음이 연결되어있으니까 풋터를 현재 풋터로 설정해도되었는데 이 케이스는 해더를 앞으로 옮기면 블록이 연속된게 아니니까 next로 재조정해야한다

        bp=PREV_BLKP(bp);
    }
    return bp;
}

static void *find_fit(size_t asize){ //asize를 만족할 수 있는 빈 블록(free block) 을 찾아주는 함수, return: 조건에 맞는 블록 포인터, 없으면 NULL
    //first-fit
    void *bp; //지금 검사하고 있는 블록의 포인터
    for (bp=heap_listp;GET_SIZE(HDRP(bp))>0; bp=NEXT_BLKP(bp)){ 
        //heap_listp: 힙의 첫 번째 블록 포인터 (전역변수),	HDRP(bp): 현재 블록의 헤더 주소. 
        //GET_SIZE(HDRP(bp)) > 0: 블록 크기가 0이면 에필로그니까, 힙의 끝. 그 전까지 탐색
        //bp = NEXT_BLKP(bp) 다음 블록으로 이동.
        if (!GET_ALLOC(HDRP(bp))&&(asize<=GET_SIZE(HDRP(bp)))){ 
            return bp;
        //가용영역이고 asize이상이면 여기 쓸수있음!
        }
    }
    return NULL;

}

static void place(void *bp, size_t asize)
{
    size_t csize=GET_SIZE(HDRP(bp));//현재 블록 크기 저장

    if ((csize-asize) >= (2*DSIZE)){ //블록을 잘라서 남기는 것이 최소 블록 크기(16바이트) 이상이면 쪼갤 수 있다
        PUT(HDRP(bp), PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));
        // 남은 공간으로 새로운 free 블록 만들기
        bp=NEXT_BLKP(bp);
        PUT(HDRP(bp),PACK(csize-asize,0));
        PUT(FTRP(bp), PACK(csize-asize,0));
    }
    else{ //남은 공간이 작으면 쪼개지 않고 현재 블록 전체(csize)를 할당 표시만 해준다.
        PUT(HDRP(bp), PACK(csize,1));
        PUT(FTRP(bp), PACK(csize,1));
    }
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 frees a block and uses boundary-tag coalescing to merge it with any adjacent free blocks in constant time
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