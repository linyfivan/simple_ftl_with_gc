#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>



#define N_PHY_BLOCKS    150     //number of physical blocks in disk
#define N_LOG_BLOCKS    100     //number of logical blocks in disk (< N_PHY_BLOCKS)
#define N_PAGE          100     //number of page in a block

int l_to_p[N_LOG_BLOCKS][N_PAGE]; //page table: [lb][lp] -> physical address(by page addressing); initialize to -1
int p_to_l[N_PHY_BLOCKS][N_PAGE];  
int active_block=0;
int active_page=0;
int physical[N_PHY_BLOCKS][N_PAGE];
int clean_counter=N_PHY_BLOCKS-1;   
bool is_valid_page[N_PHY_BLOCKS][N_PAGE]; // f: invalid/clean, t: valid 
bool clean[N_PHY_BLOCKS]; // f: invalid/valid, t: clean
/*@ ghost
    int ghost_logical[N_LOG_BLOCKS][N_PAGE];
*/


void _w(int d, int pb, int pg);
int _r(int pb, int pg);
void _erase_block(int pb);

void init( int arr_l_to_p[N_LOG_BLOCKS][N_PAGE], int arr_is_valid_page[N_PHY_BLOCKS][N_PAGE] );
int read(int lb, int lp);
void write(int d, int lb, int lp);
void gc();
int find_vb(int start_idx, int end_idx);
void erase_block_data(int idx);

/*@ 
    requires \valid( arr_l_to_p+(0..(N_LOG_BLOCKS-1)) );
	requires \valid( arr_l_to_p[0 .. (N_LOG_BLOCKS-1)]+(0..(N_PAGE-1)) );
    requires \valid( arr_is_valid_page+(0..(N_PHY_BLOCKS-1)) );
	requires \valid( arr_is_valid_page[0 .. (N_PHY_BLOCKS-1)]+(0..(N_PAGE-1)) );

    assigns clean[0 .. (N_PHY_BLOCKS-1)], arr_l_to_p[0 .. (N_LOG_BLOCKS-1)][0..(N_PAGE-1)], arr_is_valid_page[0 .. (N_PHY_BLOCKS-1)][0..(N_PAGE-1)];
    assigns active_block, active_page, clean_counter; 

    ensures 0 <= active_block < N_PHY_BLOCKS && 0 <= active_page < N_PAGE;
    ensures 1 <= clean_counter < N_PHY_BLOCKS;
*/
void init( int arr_l_to_p[N_LOG_BLOCKS][N_PAGE], int arr_is_valid_page[N_PHY_BLOCKS][N_PAGE] ) {
        

     /*@ loop invariant 0 <= i <= N_LOG_BLOCKS;
        loop assigns i, arr_l_to_p[0 .. (N_LOG_BLOCKS-1)][0..(N_PAGE-1)];
        loop variant N_LOG_BLOCKS - i; */
    for(int i=0; i<N_LOG_BLOCKS; i++) {
        /*@ loop invariant 0 <= j <= N_PAGE;
            loop assigns j, arr_l_to_p[i][0..(N_PAGE-1)];
            loop variant N_PAGE - j; */
        for(int j=0; j<N_PAGE; j++) {
            arr_l_to_p[i][j] = -1;
        }
    }

    /*@ loop invariant 0 <= i <= N_PHY_BLOCKS;
        loop assigns i, arr_is_valid_page[0 .. (N_PHY_BLOCKS-1)][0..(N_PAGE-1)];
        loop variant N_PHY_BLOCKS - i; */
    for(int i=0; i<N_PHY_BLOCKS; i++) {
        /*@ loop invariant 0 <= j <= N_PAGE;
            loop assigns j, arr_is_valid_page[i][0..(N_PAGE-1)];
            loop variant N_PAGE - j; */
        for(int j=0; j<N_PAGE; j++) {
            arr_is_valid_page[i][j] = false;
        }
    }

    /*@ loop invariant 0 <= i <= N_PHY_BLOCKS;
        loop assigns i, clean[0 .. (N_PHY_BLOCKS-1)];
        loop variant N_PHY_BLOCKS - i; */
    for(int i=0; i<N_PHY_BLOCKS; i++) {
        clean[i] = true;
    }

    active_block=0;
    active_page=0;
    clean_counter=N_PHY_BLOCKS-1;
    arr_is_valid_page[active_block][active_page] = true;
    clean[active_block] = false;
}

/*@ requires 0 <= pb < N_PHY_BLOCKS && 0 <= pg < N_PAGE;
    requires \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS*N_PAGE;
    requires \forall integer i,j; 0 <= i < N_PHY_BLOCKS && 0 <= j < N_PAGE ==> 0 <= p_to_l[i][j] < N_LOG_BLOCKS*N_PAGE;
    ensures physical[pb][pg] == d;
    ensures \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS*N_PAGE;
    ensures \forall integer i,j; 0 <= i < N_PHY_BLOCKS && 0 <= j < N_PAGE ==> 0 <= p_to_l[i][j] < N_LOG_BLOCKS*N_PAGE;
    assigns physical[pb][pg];
*/
void _w(int d, int pb, int pg){
    physical[pb][pg]=d;
}

/*@ requires 0 <= pb < N_PHY_BLOCKS ;
    requires 0 <= pg < N_PAGE;
    ensures \result == physical[pb][pg];
    assigns \nothing;
*/
int _r(int pb, int pg){
    return physical[pb][pg];
}

/*@ 
    assigns \nothing;
*/
void _erase_block(int pb){
    //pass
}

/*
*   read major function
*   :param lb: logical block
*   :param lp: logical page
*   :return: return data in the page
*/
/*@ requires 0 <= lb < N_LOG_BLOCKS && 0 <= lp < N_PAGE;
    requires 0 <= l_to_p[lb][lp] < N_PHY_BLOCKS*N_PAGE;

    requires physical[(l_to_p[lb][lp] / N_PAGE)][(l_to_p[lb][lp] % N_PAGE)] == ghost_logical[lb][lp];
    
    ensures \result == ghost_logical[lb][lp];
    assigns \nothing;
*/
int read(int lb, int lp){
    int pa = l_to_p[lb][lp];    //lookup page table to get physical address (page addressing)
    int pb = pa / N_PAGE;   //get physical block
    int pp = pa % N_PAGE;   //get physical page
    int data = _r(pb, pp);  //use api to read from the address
    return data;
}

/*
* write major function
*    :param d: data
*    :param lb: logical block
*    :param lp: logical page
*/
/*@ requires 0 <= lb < N_LOG_BLOCKS && 0 <= lp < N_PAGE;
    requires 0 <= active_block < N_PHY_BLOCKS && 0 <= active_page < N_PAGE;
    requires 1 <= clean_counter < N_PHY_BLOCKS;
    requires \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS*N_PAGE;
    requires \forall integer i,j; 0 <= i < N_PHY_BLOCKS && 0 <= j < N_PAGE ==> 0 <= p_to_l[i][j] < N_LOG_BLOCKS*N_PAGE;

    ensures 0 <= active_block < N_PHY_BLOCKS && 0 <= active_page < N_PAGE;
    ensures 0 <= l_to_p[lb][lp] < N_PHY_BLOCKS*N_PAGE;
    ensures 0 <= p_to_l[\old(active_block)][\old(active_page)] < N_LOG_BLOCKS*N_PAGE;
    ensures \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS*N_PAGE;
    ensures \forall integer i,j; 0 <= i < N_PHY_BLOCKS && 0 <= j < N_PAGE ==> 0 <= p_to_l[i][j] < N_LOG_BLOCKS*N_PAGE;
    ensures 1 <= clean_counter < N_PHY_BLOCKS;

    ensures physical[(l_to_p[lb][lp] / N_PAGE)][(l_to_p[lb][lp] % N_PAGE)] == ghost_logical[lb][lp];
    assigns l_to_p[lb][lp], p_to_l[active_block][active_page], physical[active_block][active_page], active_block, active_page, clean[0..(N_PHY_BLOCKS-1)], clean_counter; 
    assigns ghost_logical[lb][lp];
*/
void write(int d, int lb, int lp)
{

    /*@ ghost
        ghost_logical[lb][lp] = d;
    */
    
    //@assert \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS*N_PAGE;
    //@assert \forall integer i,j; 0 <= i < N_PHY_BLOCKS && 0 <= j < N_PAGE ==> 0 <= p_to_l[i][j] < N_LOG_BLOCKS*N_PAGE;
    l_to_p[lb][lp] = active_block * N_PAGE + active_page;
    
    //@assert 0 <= l_to_p[lb][lp] < N_PHY_BLOCKS*N_PAGE;
    //@assert \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE && i!= lb && j != lp ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS*N_PAGE;
    //@assert \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE && i== lb && j == lp ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS*N_PAGE;
    //@assert \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS*N_PAGE;
    p_to_l[active_block][active_page] = lb*N_PAGE+lp;

    _w(d, active_block, active_page);
    active_page++;
    if(active_page==N_PAGE){
        clean_counter--;

        active_page=0;
        active_block++;
        if(active_block==N_PHY_BLOCKS){
            active_block=0;
        }
    }

    if(clean_counter<1) {
        gc();
    }

}


/*@ requires 0 <= clean_counter < 1;
    requires 0 <= active_block < N_PHY_BLOCKS && 0 <= active_page < N_PAGE;
    requires \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS*N_PAGE;
    requires \forall integer i,j; 0 <= i < N_PHY_BLOCKS && 0 <= j < N_PAGE ==> 0 <= p_to_l[i][j] < N_LOG_BLOCKS*N_PAGE;

    ensures 1 <= clean_counter < N_PHY_BLOCKS;
    ensures 0 <= active_block < N_PHY_BLOCKS && 0 <= active_page < N_PAGE;
    ensures \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS*N_PAGE;
    ensures \forall integer i,j; 0 <= i < N_PHY_BLOCKS && 0 <= j < N_PAGE ==> 0 <= p_to_l[i][j] < N_LOG_BLOCKS*N_PAGE;

    assigns clean[0..(N_PHY_BLOCKS-1)], clean_counter;
*/
void gc() {
    int v_idx = find_vb(0, N_PHY_BLOCKS-1);
    erase_block_data(v_idx);
    
}

/*@ requires 0 <= start_idx <= end_idx < N_PHY_BLOCKS;
    ensures 0 <= \result < N_PHY_BLOCKS;
    assigns \nothing;
*/
int find_vb(int start_idx, int end_idx){
    int idx = start_idx;
    int vic_idx = idx;
    int n_of_max_invalid_or_clean_page = 0;
    
    /*@ loop invariant 0 <= idx <= end_idx < N_PHY_BLOCKS;
        loop invariant 0 <= vic_idx <= idx < N_PHY_BLOCKS;
        loop assigns idx,  n_of_max_invalid_or_clean_page, vic_idx;
        loop variant end_idx - idx; */
    while(idx != end_idx){

        if(clean[idx] == true){
            idx += 1;
            continue;
        }

        int n_of_invalid_or_clean_page = 0;

        /*@ loop invariant 0 <= pp <= N_PAGE;
            //loop invariant \at(n_of_invalid_or_clean_page, LoopEntry) == 0;
           // loop invariant \at(n_of_invalid_or_clean_page, LoopCurrent) <= \at(n_of_invalid_or_clean_page, Here) <= \at(n_of_invalid_or_clean_page, LoopCurrent)+1;
            loop invariant n_of_invalid_or_clean_page<=pp;
            loop assigns pp, n_of_invalid_or_clean_page;
            loop variant N_PAGE - pp; */
        for(int pp = 0 ; pp < N_PAGE ; pp++){
            if(is_valid_page[idx][pp] == false){
                n_of_invalid_or_clean_page +=1;
            }
        }

        if(n_of_invalid_or_clean_page >= n_of_max_invalid_or_clean_page){
            vic_idx = idx;
            n_of_max_invalid_or_clean_page = n_of_invalid_or_clean_page;
        }
        idx++;
    }
    return vic_idx;
}

/*@ requires 0 <= idx < N_PHY_BLOCKS;
    requires 0 <= clean_counter < 1;
    requires \forall integer j; 0 <= j < N_PAGE ==> 0 <= p_to_l[idx][j] < N_LOG_BLOCKS*N_PAGE;
    requires 0 <= active_block < N_PHY_BLOCKS && 0 <= active_page < N_PAGE;
    requires \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS*N_PAGE;
    requires \forall integer i,j; 0 <= i < N_PHY_BLOCKS && 0 <= j < N_PAGE ==> 0 <= p_to_l[i][j] < N_LOG_BLOCKS*N_PAGE;

    ensures 0 <= active_block < N_PHY_BLOCKS && 0 <= active_page < N_PAGE;
    ensures 1 <= clean_counter < N_PHY_BLOCKS;
    ensures \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS*N_PAGE;
    ensures \forall integer i,j; 0 <= i < N_PHY_BLOCKS && 0 <= j < N_PAGE ==> 0 <= p_to_l[i][j] < N_LOG_BLOCKS*N_PAGE;

    assigns clean[idx], clean_counter;
    
*/
void erase_block_data(int idx){
    int pb = idx;
    int pp = 0;
    
    //update clean counter first so that gc() will not triggered when write()
    clean_counter++;
    //@assert \forall integer j; 0 <= j < N_PAGE ==> 0 <= p_to_l[pb][j] < N_LOG_BLOCKS*N_PAGE;
    /*@ loop invariant 0 <= pp <= N_PAGE;
        loop invariant 0 <= pb == idx < N_PHY_BLOCKS;
        //loop invariant 0 <= p_to_l[pb][pp] < N_LOG_BLOCKS*N_PAGE;
        loop assigns pp;
        loop variant N_PAGE - pp; 
    */
    while(pp != N_PAGE){
        if(is_valid_page[pb][pp]){
            int la = p_to_l[pb][pp]; //get logical addr
            int lb = la / N_PAGE; //get logical block id
            int lp = la % N_PAGE;   //get logical page offset
            //_write(_r(pb,pp), lb, lp);
        }
        pp++;
    }
    
    //erase the block by disk erase API
    _erase_block(pb);
    //update block clean status
    clean[pb] = true;
    
}





int main(void){


    write(100,0,0);
    write(99,0,0);
    write(99,0,0);
    write(97,0,0);
    read(0, 0);
    
    //printf("%d\n",read(0,0));
}