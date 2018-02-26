#define MAXN 30009

ll dist(pii x, pii y)
{
    ll ans = ((ll)(x.fst-y.fst)*(ll)(x.fst-y.fst)) + ((ll)(x.snd-y.snd)*(ll)(x.snd-y.snd));
    return ans;
}

vector<pii> save;
int n;

ll dist_min;
void ClosestPair(int b,int e)
{
    if(b==e) return;
    else
    {
        int mid = (b+e)/2 ;

        ClosestPair(b,mid);
        ClosestPair(mid+1,e);

        ll x_mid = save[mid].fst;

        vector<pii > save1;//ordenar por Y

        f(i,b,e+1)
        if( (ll)(save[i].fst - x_mid)*(ll)(save[i].fst - x_mid) <= dist_min )
            save1.pb(pii(save[i].snd,save[i].fst) );

        sort(all(save1));
        f(i,0,save1.size() )
        {
            int ind1 = i+1; // ind1++
            int cont = 0;
            while(ind1<save1.size() && cont<6)
            {
                dist_min = min(dist_min , dist( save1[i], save1[ind1] ) );
                ind1++;
                cont++;
            }
        }
    }
}

int main()
{
    freopen("in.c","r",stdin);
    int x,y;
    scanf("%d",&n);
    f(i,0,n)
    {
        scanf("%d%d",&x,&y);
        save.pb(pii(x,y));
    }
    sort(all(save));
    dist_min = 1000000000LL;
    ClosestPair(0,n-1);
    printf("%.6lf\n",sqrt(dist_min));
    return 0;
}
