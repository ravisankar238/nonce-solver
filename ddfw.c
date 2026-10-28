// DDFW (divide and distribute fixed weights) for k-SAT. usage: ddfw file.cnf seed maxsec [1=random | initfile] [init=8] [p0=0.15]
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#define K 5
static unsigned long long rs;
static inline unsigned long long rnd(){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
static inline double urand(){return (rnd()>>11)*(1.0/9007199254740992.0);}
int n,m,*C,*st,*occ,*ns,*cr,*un,*wh,nu;long long *w,*mk,*bk;char*a;
static void flip(int v){
  int tl=a[v]?v:-v; a[v]^=1; int fl=-tl;
  for(int q=st[fl+n];q<st[fl+n+1];q++){int i=occ[q]; long long wi=w[i];
    if(ns[i]==0){int x=wh[i],last=un[--nu];un[x]=last;wh[last]=x;wh[i]=-1;
      for(int j=0;j<K;j++)mk[abs(C[i*K+j])]-=wi; bk[v]+=wi;}
    else if(ns[i]==1) bk[cr[i]]-=wi;
    ns[i]++;cr[i]^=v;}
  for(int q=st[tl+n];q<st[tl+n+1];q++){int i=occ[q]; long long wi=w[i]; ns[i]--;cr[i]^=v;
    if(ns[i]==0){un[nu]=i;wh[i]=nu++; bk[v]-=wi; for(int j=0;j<K;j++)mk[abs(C[i*K+j])]+=wi;}
    else if(ns[i]==1) bk[cr[i]]+=wi;}
}
static inline void addw(int i,long long d){ w[i]+=d;
  if(ns[i]==0){for(int j=0;j<K;j++)mk[abs(C[i*K+j])]+=d;}
  else if(ns[i]==1) bk[cr[i]]+=d; }
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); if(fscanf(f,"%d %d",&n,&m)!=2)return 1;
  rs=atoll(argv[2])*2654435761ULL+987654321ULL; for(int i=0;i<10;i++)rnd(); double maxsec=atof(argv[3]);
  long long W0=argc>5?atoll(argv[5]):8; double p0=argc>6?atof(argv[6]):0.15;
  C=malloc(sizeof(int)*m*K);
  for(int i=0;i<m*K;i++) if(fscanf(f,"%d",&C[i])!=1) return 1;
  int*cnt=calloc(2*n+2,sizeof(int)); for(int i=0;i<m*K;i++)cnt[C[i]+n]++;
  st=calloc(2*n+3,sizeof(int)); for(int i=0;i<2*n+2;i++)st[i+1]=st[i]+cnt[i];
  occ=malloc(sizeof(int)*st[2*n+2]); int*pp=malloc(sizeof(int)*(2*n+3)); for(int i=0;i<2*n+3;i++)pp[i]=st[i];
  for(int i=0;i<m;i++)for(int j=0;j<K;j++){int l=C[i*K+j]+n;occ[pp[l]++]=i;}
  a=calloc(n+1,1); char*ba=calloc(n+1,1);
  for(int v=1;v<=n;v++)a[v]=rnd()&1;
  if(argc>4 && atoi(argv[4])!=1){FILE*g=fopen(argv[4],"r");for(int v=1;v<=n;v++){int ch=fgetc(g);a[v]=ch=='1';}fclose(g);}
  ns=calloc(m,sizeof(int));cr=calloc(m,sizeof(int));un=malloc(sizeof(int)*m);wh=malloc(sizeof(int)*m);
  w=malloc(sizeof(long long)*m);mk=calloc(n+1,sizeof(long long));bk=calloc(n+1,sizeof(long long));
  for(int i=0;i<m;i++)w[i]=W0;
  nu=0;
  for(int i=0;i<m;i++){int s=0,x=0;for(int j=0;j<K;j++){int l=C[i*K+j],v=abs(l);if(a[v]==(l>0)){s++;x^=v;}}ns[i]=s;cr[i]=x;wh[i]=-1;
    if(!s){un[nu]=i;wh[i]=nu++;for(int j=0;j<K;j++)mk[abs(C[i*K+j])]+=W0;} else if(s==1)bk[x]+=W0;}
  int*cand=malloc(sizeof(int)*m*K);
  clock_t t0=clock(); long long it=0,fl=0,tr=0; int best=nu; for(int v=1;v<=n;v++)ba[v]=a[v];
  while(nu){
    if((it&0x3FFFF)==0){double el=(double)(clock()-t0)/CLOCKS_PER_SEC;
      if(((it>>18)&63)==0)fprintf(stderr,"t=%.0f nu=%d best=%d flips=%lld transfers=%lld\n",el,nu,best,fl,tr);
      if(el>maxsec){fprintf(stderr,"timeout nu=%d best=%d flips=%lld\n",nu,best,fl);for(int v=1;v<=n;v++)putchar(ba[v]?'1':'0');putchar('\n');return 2;}}
    it++;
    long long bs=-(1LL<<60); int nc=0;
    for(int u=0;u<nu;u++){int i=un[u];for(int j=0;j<K;j++){int v=abs(C[i*K+j]);long long s=mk[v]-bk[v];
      if(s>bs){bs=s;nc=0;cand[nc++]=v;} else if(s==bs)cand[nc++]=v;}}
    if(bs>0 || (bs==0 && urand()<p0)){ flip(cand[rnd()%nc]); fl++; if(nu<best){best=nu;for(int v=1;v<=n;v++)ba[v]=a[v];} continue; }
    // weight transfer
    tr++;
    int nuu=nu; for(int u=0;u<nuu;u++){int i=un[u];
      int bj=-1; long long bw=-1;
      for(int j=0;j<K;j++){int l=C[i*K+j]; for(int q=st[l+n];q<st[l+n+1];q++){int c=occ[q]; if(ns[c]>0 && w[c]>bw){bw=w[c];bj=c;}}}
      if(bj<0 || bw<=W0 || urand()<0.01){ // random satisfied clause with weight > init
        for(int tries=0;tries<100;tries++){int c=rnd()%m; if(ns[c]>0 && w[c]>W0){bj=c;bw=w[c];break;}}
      }
      if(bj<0 || bw<=1) continue;
      long long d = bw>W0?2:1;
      addw(bj,-d); addw(i,d);
    }
  }
  for(int v=1;v<=n;v++)putchar(a[v]?'1':'0'); putchar('\n');
  fprintf(stderr,"solved flips=%lld sec=%.1f\n",fl,(double)(clock()-t0)/CLOCKS_PER_SEC);
  return 0;
}
