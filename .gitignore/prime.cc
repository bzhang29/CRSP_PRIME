///@file CRSP_PRIME.cpp
///@brief Implementation of the Deleglise-Rivat prime counting algorithm
///       In Deleglise-Rivat algorithm there were S_1, S_2 and S_3
///       needed to be compute in the special leaves. We also used some 
///       ideas from Kim Walisch https://github.com/kimwalisch/primecount.

///       The implementation is based on the paper:
///       Marc Deléglise and Jöel Rivat,COMPUTING pi(x): THE MEISSEL, LEHMER, LAGARIAS,
///       MILLER, ODLYZKO METHOD, 
///       Math. Comp, 65, number 33, (1996), 235–245.


#include <iostream>
#include <cmath>
#include <array>
#include <numeric>
#include <limits>
#include <vector>
#include <utility>
#include <algorithm>
#include <cstdint>
#define C 6 
using namespace std;

class prime{
    private:
        int64_t x;
        int64_t sqx;
        int64_t cbx;
        int64_t qtx;
        constexpr static size_t product_c[7]={1,2,6,30,210,2310,30030}; //prod from p_0=1 to p_C=13
        constexpr static size_t totient[7]={1,1,2,8,48,480,5760};  //(p_1-1)*...*(p_c-1)   c = 1,..,C
        vector<int64_t> primes;
        vector<int64_t> pi;
        vector<int64_t> lpf; // mu*p_min
        void init(vector<char> &, int64_t);
    public:
        prime(int64_t);
        ~prime(){};
        int64_t min(int64_t,int64_t);
        int64_t min3(int64_t,int64_t,int64_t);
        int64_t max3(int64_t,int64_t,int64_t);
        int64_t max(int64_t,int64_t);
        int64_t squarert(int64_t);
        int64_t cubicrt(int64_t);
        int64_t quarticrt(int64_t);
        int64_t phi(int64_t,int64_t);
        int64_t s0();
        int64_t s();
        int64_t s1();
        int64_t s2();
        int64_t s2_u();
        int64_t s2_v();
        int64_t s3();
        int64_t prime_pi();
        vector<char> gen_sieve(int64_t);
};
/// We assume y=x^(1/2)
/// Sieve the array up to y and generate primes within this range
prime::prime(int64_t n):x(n)
{
    sqx = squarert(x);
    cbx = cubicrt(x);
    qtx = quarticrt(x);
    int64_t n_primes=sqx; 
    vector<char> sieve = gen_sieve(n_primes);
    init(sieve, n_primes);
}

/// Using Sieve of Eratosthenes to cross off all the multiples of prime.
vector<char> prime::gen_sieve(int64_t max){
    vector<char> sieve(max+1,1);
    sieve[0] = 0;
    sieve[1] = 0;
    int64_t sqmax=squarert(max);
    for(int64_t i=2;i<=sqmax;++i)
    {
        if(sieve[i]){
            for(int64_t j=i*i;j<=max;j+=i) sieve[j]=0;
        }
    }
    return sieve;    
}

/// We use sieve data to generate pi(n), mu(n), p_min(n) and primes for a given range.
/// We also combine mu(n) and p_min(n) since mu(n) = {-1,0,1}
/// By convention: pi(0) = pi(1) = 0, p_0 = 1, mu(0)p_min(0) = 0, mu(1)p_min(1) = infty
void prime::init(vector<char> & sieve, int64_t a)
{
    int64_t count = 0;
    pi.resize(a+1);
    pi[0]=0;
    pi[1]=0;
    for(int64_t i=2;i<=a;++i)
    {
        if(sieve[i]) ++count;
        pi[i]=count;
    }
    primes.resize(count+1); 
    primes[0]=1;
    for(int64_t i=2,j=0;i<=a;++i)
    {
        if(sieve[i])
            primes[++j]=i;
    }
    lpf.resize(a + 1, 1);
    int64_t pi_sqa=pi[squarert(a)];
    int64_t pi_a=pi[a];
    lpf[0]=0;
    lpf[1] = numeric_limits<int64_t>::max();
    for(int64_t i=1,p,p2; i<=pi_sqa && (p=primes[i],p2=p*p,p2<=a);++i){
        for(int64_t j=p2;j<=a;j+=p2){ // j : multiples of p^2
            lpf[j]=0;//set as non-square_free.
        }
    }
    for(int64_t i=1,p;i<=pi_a;++i){
        p=primes[i];
        for(int64_t j=p;j<=a;j+=p){ // j : multiples of prime p
            if(lpf[j]==0) continue;
            if(lpf[j]==1){ 
                lpf[j]=-p; //min prime
            }
            else{
                lpf[j]*=-1;//flip
            }
        }
    }

}
int64_t prime::max(int64_t a,int64_t b){return(a>b)?a:b;};
int64_t prime::min(int64_t a,int64_t b){return(a<b)?a:b;};
int64_t prime::min3(int64_t a,int64_t b,int64_t c)
{
    int64_t current_min = min(a,b);
    return min(current_min,c);
}
int64_t prime::max3(int64_t a,int64_t b,int64_t c)
{
    int64_t current_max = max(a,b);
    return max(current_max,c);
}

int64_t prime::squarert(int64_t x)
{
    int64_t t=sqrt(x);
    return ((t+1)*(t+1)==x) ? t+1:t;
}

int64_t prime::cubicrt(int64_t x)
{
    int64_t t = cbrt(x);
    return (((t+1)*(t+1)*(t+1)==x))? t+1:t;
}

int64_t prime::quarticrt(int64_t x)
{
    int64_t t = pow(x,0.25);
    return (((t+1)*(t+1)*(t+1)*(t+1))==x)? t+1:t;
}

/// Using the S_0 formula to compute the contribution of 
/// ordinary leaves
/// Ordinary leaves: mu(n)phi(x/n,b) if b=0 and n <= y
/// S_0 = \sum_{n <= y}{ mu(n)(x/n) }
int64_t prime::s0()
{
    int64_t sum = 0;
    for(int64_t m=1;m<=sqx;++m)
    {
        int64_t n = x/m;
        if(lpf[m]==0) continue;
        sum = (lpf[m]>0) ? sum+n:sum-n;
    }
    return sum;
}

/// Using store pi(y), we can easily compute S_1 with a constant time
int64_t prime::s1()
{
    int64_t pi_sqx = pi[sqx];
    int64_t pi_cbx = pi[cbx];
    return (pi_sqx - pi_cbx) * (pi_sqx - pi_cbx -1)/2;
}

/// Deleglise-Rivat splits S_2 into U and V 
/// based on q > x/p^2 or q <= x/p^2
/// U part has the condition q > x/p^2
/// The condition implies p^2 > x/p >= x/y and p > (x/y)^1/2
int64_t prime::s2_u(){
    int64_t sum = 0;
    int64_t pi_sqx = pi[sqx];  
    int64_t pi_cbx = pi[cbx];
    int64_t pi_qtx = pi[qtx];
    for(int64_t p,i=pi_qtx+1;i<=pi_cbx;++i)
    {
        p=primes[i];
        sum += pi_sqx - pi[x/(p*p)];
    }
    return sum;
}

/// The contribution of S2
/// V has the condition q <= x / p^2
/// It implies p <= x / pq < x^1/2 < p^2
int64_t prime::s2_v(){
    int64_t sum = 0;
    int64_t pi_qtx=pi[qtx];
    int64_t pi_cbx=pi[cbx];
    for(int64_t i=pi_qtx+1,p;i<=pi_cbx;++i)
    {
        p=primes[i];
        for(int64_t j = i+1,q; j<= pi[x/(p*p)];++j)// p<q=primes[j] && q<=x/p^2
        {
            q=primes[j];
            sum += 2 + pi[x/(p*q)]-i;//  2-pi[ p=primes[i] ]+ pi [x/(p*q)]=2-i+pi[x/(p*q)]
        }
    }
    return sum;
}

/// The contribution of S2
int64_t prime::s2()
{
    return s2_u() + s2_v();
}

/// The contribution of S3
/// S3 needs to sieve out the interval [1,x/y] by primes
/// In our case, we sieve out the interval [1,x^1/2]
/// After sieving p_{b-1} we sum -mu(m)phi(x/mp,b-1)
int64_t prime::s3()
{
    int64_t limit = sqx +1;
    int64_t sum = 0;
    int64_t pi_sqx = pi[sqx];
    int64_t pi_cbx = pi[cbx];
    int64_t pi_qtx = pi[qtx];
    vector<char> segment_sieve(limit,1);
    segment_sieve[0]=0;//Turn off zero case.(ignore i=0 case)
    for(int64_t b = 1,p;b<=pi_qtx;++b)
    {
        p = primes[b];
        //sum_{p_min[m]>p && m<=sqx<m*p} mu(m)*phi(x/(m*p),b-1)
        // we need (b-1)- elementary sieve operations.
        for(int64_t i=1,j,v_phi=0, m = sqx; m > sqx/p ;--m)
        {
            if(lpf[m]==0 || (-p<=lpf[m] && lpf[m]<=p ) ) continue;
            // p_min > p 
            {
                // Let m' be the previous m satisfying above conditions.
                //computing phi(x/(p*m),b-1)=phi(x/(p*m')+sum_{ x/(p*m') < i <=x/(p*m)}(segment_sieve[i])
                j=x/(p*m)+1;// [  , ) 
                v_phi +=std::accumulate(&segment_sieve[i],&segment_sieve[j],0);
                i=j;              
                sum =  (lpf[m]>0) ? sum-v_phi: sum+v_phi;//+- sign represents mu.    
            }
        }
        //Turn off multiple of p: bth-elementary sieve operationn
        for(int64_t k = p;k<limit;k+=p)
            segment_sieve[k] = 0;
    }
    return sum;
}

/// The contribution of special leaves
int64_t prime::s(){
    return s1()+s2()+s3();
}

/// pi(x) = phi(x,a) + a - 1 - phi_2(x,a)
/// We pick a = x^1/2, then phi_2(x,a) = 0 with a = pi(x^1/2)
/// pi(x,a) = phi(x,a) + a - 1
int64_t prime::prime_pi(){
    int64_t phi_x_a = s0()+s();
    return  phi_x_a+pi[sqx] - 1;
}

int main(int argc, char** argv){
    size_t i=1;
    size_t c=1;
    if(argc>1){
        i= stoi(argv[1]);
        if(argc>2) c=stoi(argv[2]);
    }
    int64_t x = c*pow(10,i);
    prime p(x);
    cout<<"pi("<<c<<"*10^"<<i<<")="<<p.prime_pi()<<endl;
}
