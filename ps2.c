// probSAT for k-SAT. usage: ps file.cnf seed cb maxsec  ; input: "n m" then m lines of k literals ; output: assignment string
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#define K 5
static unsigned long long rs;
static inline unsigned long long rnd(){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); int n,m; if(fscanf(f,"%d %d",&n,&m)!=2)return 1;
  rs=atoll(argv[2])*2654435761ULL+12345; double cb=atof(argv[3]); double maxsec=atof(argv[4]);
  int*C=malloc(sizeof(int)*m*K);
  for(int i=0;i<m*K;i++) if(fscanf(f,"%d",&C[i])!=1) return 1;
  int*cnt=calloc(2*n+2,sizeof(int)); for(int i=0;i<m*K;i++)cnt[C[i]+n]++;
  int*st=calloc(2*n+3,sizeof(int)); for(int i=0;i<2*n+2;i++)st[i+1]=st[i]+cnt[i];
  int*occ=malloc(sizeof(int)*st[2*n+2]); int*pp=malloc(sizeof(int)*(2*n+3)); for(int i=0;i<2*n+3;i++)pp[i]=st[i];
  for(int i=0;i<m;i++)for(int j=0;j<K;j++){int l=C[i*K+j]+n;occ[pp[l]++]=i;}
  char*a=calloc(n+1,1); char*ba=calloc(n+1,1); int*sc=calloc(n+1,sizeof(int));
  for(int i=0;i<m*K;i++){int l=C[i];sc[abs(l)]+=l>0?1:-1;}
  for(int v=1;v<=n;v++)a[v]=sc[v]>0?1:(sc[v]<0?0:(rnd()&1));
  if(argc>5 && atoi(argv[5])==1) for(int v=1;v<=n;v++)a[v]=rnd()&1;
  else if(argc>5){FILE*g=fopen(argv[5],"r");for(int v=1;v<=n;v++){int ch=fgetc(g);a[v]=ch=='1';}fclose(g);}
  int*ns=calloc(m,sizeof(int)),*cr=calloc(m,sizeof(int)),*un=malloc(sizeof(int)*m),*wh=malloc(sizeof(int)*m),*br=calloc(n+1,sizeof(int));
  double lut[256]; for(int b=0;b<256;b++)lut[b]=pow(1.0+b,-cb);
  int nu=0;
  for(int i=0;i<m;i++){int s=0,x=0;for(int j=0;j<K;j++){int l=C[i*K+j],v=abs(l);if(a[v]==(l>0)){s++;x^=v;}}ns[i]=s;cr[i]=x;wh[i]=-1;if(!s){un[nu]=i;wh[i]=nu++;} else if(s==1)br[x]++;}
  clock_t t0=clock(); long long fl=0; int best=nu;
  while(nu){
    if((fl&0xFFFFF)==0){double el=(double)(clock()-t0)/CLOCKS_PER_SEC; if(el>maxsec){fprintf(stderr,"timeout nu=%d best=%d flips=%lld\n",nu,best,fl);for(int v=1;v<=n;v++)putchar(ba[v]?'1':'0');putchar('\n');return 2;}}
    int ci=un[rnd()%nu]; double p[K],tot=0;
    for(int j=0;j<K;j++){int b=br[abs(C[ci*K+j])];p[j]=lut[b>255?255:b];tot+=p[j];}
    double r=(rnd()>>11)*(1.0/9007199254740992.0)*tot; int j=0; while(j<K-1&&r>p[j]){r-=p[j];j++;}
    int v=abs(C[ci*K+j]); int tl=a[v]?v:-v; a[v]^=1; int fl2=-tl;
    for(int q=st[fl2+n];q<st[fl2+n+1];q++){int i=occ[q];
      if(ns[i]==0){int w=wh[i],last=un[--nu];un[w]=last;wh[last]=w;wh[i]=-1;br[v]++;}
      else if(ns[i]==1)br[cr[i]]--;
      ns[i]++;cr[i]^=v;}
    for(int q=st[tl+n];q<st[tl+n+1];q++){int i=occ[q]; ns[i]--;cr[i]^=v;
      if(ns[i]==0){un[nu]=i;wh[i]=nu++;br[v]--;}
      else if(ns[i]==1)br[cr[i]]++;}
    fl++; if(nu<best){best=nu; for(int v=1;v<=n;v++)ba[v]=a[v];}
  }
  for(int v=1;v<=n;v++)putchar(a[v]?'1':'0'); putchar('\n');
  fprintf(stderr,"solved flips=%lld sec=%.1f\n",fl,(double)(clock()-t0)/CLOCKS_PER_SEC);
  return 0;
}
