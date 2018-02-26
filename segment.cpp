struct nodo{
    int sum, minN;
    nodo() { }
    nodo(int _sum, int _minN){
        sum = _sum;
        minN = _minN;
    }
}T[MAXN*4];

int n, a[MAXN];

void init(int b, int e, int node)
{
    if(b == e) T[node].sum = T[node].minN = a[b];
    else
    {
        int mid = (b + e)/2, le = 2*node + 1, ri = 2*node + 2;
        init(b, mid, le);
        init(mid + 1, e, ri);

        T[node].sum  = T[le].sum + T[ri].sum;
        T[node].minN = min(T[le].minN, T[ri].minN);
    }
}

void update(int b, int e, int node, int i, int val)
{
    if(i < b || i > e) return;

    if( b == e ) T[node].sum = T[node].minN = a[i] = val;
    else
    {
        int mid = (b + e)/2, le = 2*node + 1, ri = 2*node + 2;

        update(b, mid, le, i, val);
        update(mid + 1, e, ri, i, val);

        T[node].sum  = T[le].sum + T[ri].sum;
        T[node].minN  = min(T[le].minN, T[ri].minN);
    }
}


nodo query(int b, int e, int node, int i, int j)
{
    if(i <= b && e <= j) return T[node];

    int mid = (b + e) / 2, le = 2*node + 1, ri = 2*node + 2;

    if(j <= mid) return query(b, mid, le, i, j);
    else if(mid < i) return query(mid + 1, e, ri, i, j);
    else
    {
        nodo ret1 = query(b, mid, le, i, j);
        nodo ret2 = query(mid + 1, e, ri, i, j);

        nodo ret;
        ret.sum  = ret1.sum + ret2.sum;
        ret.minN = min(ret1.minN, ret2.minN);
        return ret;
    }
}


