//CENTRO DE MASA
#define MAXN 30009

struct node{
    int x;
    int damage;
    int large;

    node(){}

    node(int _x, int _damage , int _large){
        x = _x;
        damage = _damage;
        large = _large;
    }
};

#define vn vector<node>

vector< vn > AdjList;

int n,k,x,y,d,l,hijos[MAXN],mini,CM,cont,cc , ans;
bool cmp_global[MAXN];

int dfs(int nodo, int padre){// es para hallar el numero de nodos de los hijos colgado de un centro

    int ans = 1;

    f(i,0,AdjList[nodo].size()){

        int v = AdjList[nodo][i].x;
        if(!cmp_global[v]  &&  v!=padre )
            ans += dfs(v,nodo);

    }

    return hijos[nodo] = ans;

}

void dfs1(int nodo, int padre, int num_nodos){// tengo que inicializar mini con INF

    int sum = 0,maxi = -1;

    f(i,0,AdjList[nodo].size()){
        int v = AdjList[nodo][i].x;
        if(!cmp_global[v] && v!=padre){

            dfs1(v,nodo, num_nodos);
            maxi = max(maxi , hijos[v]);
            sum += hijos[v];
        }
    }

    maxi = max(maxi,  num_nodos - sum -1);

    if(mini>=maxi){
        CM = nodo;
        mini = maxi;
    }
}

vector<pair<pii,int> > acum;

void dfs2(int nodo, int padre, int damage, int large){

    cont++;
    acum.pb(make_pair(pii(damage, large) , cc   )   );
    f(i,0,AdjList[nodo].size()){

        int v = AdjList[nodo][i].x , dam = AdjList[nodo][i].damage , lar = AdjList[nodo][i].large;
        if(!cmp_global[v] && v!=padre)  dfs2(v,nodo, damage + dam , large + lar);

    }

}


vector<pii> pre_process(){

    vector<pii> save1;
    acum.clear();
    cc = 0;
    f(i,0,AdjList[CM].size()){

        int v = AdjList[CM][i].x , damage = AdjList[CM][i].damage ;
        int large = AdjList[CM][i].large;

        if(!cmp_global[v] ){
            cont = 0;
            dfs2(v , -1 , damage , large);
            save1.pb(pii(v, cont));
            cc++;

        }

    }

    return save1;

}

void sol(int nodo, int num_nodos){
    if(num_nodos==1)    return;

    mini = oo;
    //Optengo el CM
    dfs(nodo,-1);
    dfs1(nodo,-1,num_nodos);
    ///////////////////////////////

    cmp_global[CM] = true;

    vector<pii> save1 = pre_process();

    sort(all(acum));

    f(i,0,acum.size())
        if(acum[i].fst.fst<=k)
            ans = max(ans, acum[i].fst.snd);

    /////////////////////7
    vector<pii> temp;

    vector<pii> dp1,dp2;

    temp.pb(pii(acum[0].fst.snd , acum[0].snd));
    temp.pb(pii(acum[0].fst.snd , acum[0].snd));

    dp1.pb(temp[0]);
    dp2.pb(temp[1]);

    f(i,1,acum.size()){

        temp.pb(pii(acum[i].fst.snd , acum[i].snd));
        sort(rall(temp));

        vector<pii> temp1;
        temp1.pb(temp[0]);

        if(temp[1].snd != temp[0].snd)  temp1.pb(temp[1]);
        else if(temp[2].snd != temp[0].snd) temp1.pb(temp[2]);
        else    temp1.pb(temp[1]);

        temp = temp1;

        dp1.pb(temp[0]);
        dp2.pb(temp[1]);
    }

    f(i,1,acum.size()){
        int L = 0 , R = i-1 , mid;
        while( R-L > 1){
            mid = (L+R)/2;
            if(acum[i].fst.fst + acum[mid].fst.fst <= k)   L = mid;
            else    R = mid;
        }

        if(acum[R].fst.fst + acum[i].fst.fst <= k)  {
            if(dp1[R].snd!=acum[i].snd) ans = max(ans, dp1[R].fst + acum[i].fst.snd);
            if(dp2[R].snd!=acum[i].snd) ans = max(ans, dp2[R].fst + acum[i].fst.snd);
        }
        if(acum[L].fst.fst + acum[i].fst.fst <= k)  {
            if(dp1[L].snd!=acum[i].snd) ans = max(ans, dp1[L].fst + acum[i].fst.snd);
            if(dp2[L].snd!=acum[i].snd) ans = max(ans, dp2[L].fst + acum[i].fst.snd);
        }

    }

    ////////////////////////

    f(i,0,save1.size())
        sol(save1[i].fst , save1[i].snd);

}


int main() {
    freopen("in.c","r",stdin);

    int TC,NC = 1;
    scanf("%d",&TC);

    while(TC--){

        scanf("%d%d",&n,&k);
        AdjList.assign(n+2 , vn());

        f(i,0,n-1){
            scanf("%d%d%d%d",&x,&y,&d,&l);
            x--;y--;
            AdjList[x].pb( node(y,d,l)  );
            AdjList[y].pb( node(x,d,l)  );

        }

        clr(cmp_global,0);
        ans = 0;

        sol(0 ,  n ) ;

        cout<<"Case "<<NC++<<": "<<ans<<endl;

    }

    return 0;
}

