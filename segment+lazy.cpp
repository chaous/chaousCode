
struct nodo{
    ll sum;
    ll add;// acumulado para el (LP)
    nodo() { }
    nodo(ll _sum, ll  _add){
        sum = _sum;
        add = _add;
    }
}T[MAXN * 4];

int a[MAXN];

void relax(int node, int b, int e){
    T[node].sum += T[node].add*((e-b)+1);
    if(b==e){
        //T[node].add=T[b].add;
    }else{
        T[node+node+1].add += T[node].add;
        T[node+node+2].add += T[node].add;
    }
    T[node].add = 0;
}

void init(int b, int e, int node){
    if(b==e)    T[node].sum = a[b];
    int mid = (b+e)/2, le = 2*node + 1, ri = 2*node + 2;
    init(b,mid,le);
    init(mid+1,e,ri);
    T[node].sum=T[le].sum+T[ri].sum;
}

void update(int b, int e, int node, int i,int j, int val)
{   relax(node,b,e);
    if(j < b || i > e) return;
    if(i <= b && e <= j){
        T[node].add += val;
        relax(node,b,e);
        return;
    }
    int mid = (b + e)/2, le = 2*node + 1, ri = 2*node + 2;

    update(b, mid, le, i,j, val);
    update(mid + 1, e, ri, i,j, val);

    T[node].sum  = T[le].sum + T[ri].sum;
}

nodo query(int b, int e,int node, int i, int j)
{
    relax(node,b,e);
    if(i <= b && e <= j) return T[node];
    int mid = (b + e) / 2, le = 2*node + 1, ri = 2*node + 2;
    if(j<=mid)  return query(b, mid, le, i, j);
    else if(mid<i)  return query(mid + 1, e, ri, i, j);
    else{
        nodo ret;
        nodo ret1=query(b, mid, le, i, j);
        nodo ret2=query(mid + 1, e, ri, i, j);

        ret.sum=ret1.sum+ret2.sum;
        return ret;
    }
}

