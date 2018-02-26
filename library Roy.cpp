/*
** Sugerencias enviar a palacios.roy@gmail.com
30.04.2012 : v1.0 - Version inicial

30.04.2012 : V1.1 - Actualizacion del Hopcroft-Karp:
				   * Se cambia a la version descrita en wikipedia (bfs + dfs)
				   * Se incluye un 'greedy step' opcional para mejorar el tiempo de ejecucion

30.04.2012 : V1.2 - Teorema de Heron: Area y circunradio para triangulo y cuadrilatero ciclico

01.05.2012 : V1.3 - Se incluyo el LCP O(n) de hamlet en el Suffix Array O(nlogn) de E-Maxx

07.05.2012 : V1.4 - Se incluyeron funciones basicas de Trie
					* Pendiente: Implementacion de (left child, next sibling) http://apps.topcoder.com/forums/?module=Thread&threadID=686687&mc=5

25.06.2012 : V1.5 - Se simplifico de la funcion lineIntersection

29.06.2012 : V1.6 - Por algun motivo no tenia la funcion isConvex() para determinar si un poligono simple es convexo o no

14.07.2012 : V1.7 - Smallest enclosing circle y circumcenter simplificado

23.07.2012 : V1.8 - Factoradic Index

14.09.2012 : V1.9 - Suffix Automata de Emaxx sin map

19.09.2012 : V2.0 - Criba en O(n) y optimizacion sencilla de suma de cadenas en base 10

08.10.2012 : V2.1 - Test de Miller-Rabin para long long de hasta 17 digitos(modpow con modprod)

24.10.2012 : V2.2 - BIT y Segment Tree con Lazy Propagation, lo mas generico posible.

*/

//######## UTILES ########################################################################

ios::sync_with_stdio(0);

int popcount(int x)
{
	int ans = 0;
	while(x)
	{
		ans++;
		x = x & (x-1);
	}
	return ans;
}

//factoradic s = permutacion del 1 al 9
int encode(const string &s)
{
	int x = 0, k = 9;
	for(int i=0; i<9; i++)
	{
		x = k * x;
		for(int j=i+1; j<9; j++)
			if(s[j] < s[i])
				x++;
		k--;
	}
	return x;
}

//####### UNION FIND #############################################################

#define MAXN 400000

int PP[MAXN];
int F(int x) {return x == PP[x] ? x : (PP[x] = F(PP[x]));}
void U(int x, int y) {PP[F(x)] = F(y);}

#define MAXN 400000

int parent[MAXN];
int rank[MAXN];

int Find(int a)
{
	if(parent[a] == a) return a;
	return parent[a] = Find(parent[a]);
}

void Union(int a, int b)
{
	int pa = Find(a);
	int pb = Find(b);

	if(pa != pb)
	{
		if(rank[pa] < rank[pb]) parent[pa] = pb;
		else if(rank[pa] > rank[pb]) parent[pb] = pa;
		else
		{
			parent[pb] = pa;
			rank[pa]++;
		}
	}
}


//######################################################################################
//################################ TEORIA DE NUMEROS ###################################
//######################################################################################

int GCD(int a, int b)
{
	if(b==0) return a;
	return GCD(b, a%b);
}

pair <int, int> extended_GCD(int a, int b)
{
    if(a % b == 0) return make_pair(0, 1);
    else
    {
        pair <int, int> P = extended_GCD(b, a % b);
        int x = P.first;
        int y = P.second;
        return make_pair(y, x-y*(a/b));
	}
}

/*
Teorema chino del resto
-----------------------

Dados k enteros positivos {ni}, tales que ni y nj son coprimos (i!=j).
Para cualquier {ai}, existe x tal que:

x % ni = ai

Todas las soluciones son congruentes modulo N = n1*n2*...*nk

r*ni + s*N/ni = 1 -> ei = s*N/ni   -> ei % nj = 0
                     r*ni + ei = 1 -> ei % ni = 1

x = a1*e1 + a2*e2 + ... + ak*ek
*/

//########################################################################################

bool is(int n)
{
	if(n<=1) return false;
	if(n==2) return true;
	if(n%2==0) return false;

	for(int i=3; i*i<=n; i+=2)
		if(n%i==0) return false;

	return true;
}

//########################################################################################

// Criba normal
#define MAXN 100000

bool prime[MAXN+1];

void sieve()
{
	memset(prime, true, sizeof(prime));

	prime[0] = false;
	prime[1] = false;

	for(int i=2; i*i<=MAXN; i++)
		if(prime[i])
			for(int j=i*i; j<=MAXN; j+=i)
				prime[j] = false;
}

// Criba O(n) con factores primos - Usa mucha memoria
#define MAXN 1000000

int A[MAXN + 1], p[MAXN + 1], pc = 0;

void sieve()
{
	for(int i=2; i<=MAXN; i++){
		if(!A[i]) p[A[i] = ++pc] = i;
		for(int j=1; j<=A[i] && i*p[j]<=MAXN; j++)
			A[i*p[j]] = j;
	}
}

// Criba optimizada para memoria y tiempo - solo impares
#define MAXN 300000000

bitset <MAXN+1> notprime;

void sieve()
{
	for(int i=3; i*i<=MAXN; i+=2)
		if(!notprime[i])
			for(int j=i*i; j<=MAXN; j+=(i<<1))
				notprime[j] = true;
}

//#######################################################################################

vector < pair <int, int> > primeFact(int N)
{
	vector < pair <int, int> > V;

	for(int i=2; i*i<=N; i++)
	{
		int a=0;
		while(N%i==0)
		{
			N/=i;
			a++;
		}
		if(a!=0) V.push_back(make_pair(i, a));
	}
	if(N>1) V.push_back(make_pair(N, 1));

	return V;
}

//#######################################################################################

#define MAXN 10000
int phi[MAXN + 1]
for(i = 1; i <= MAXN; ++i) phi[i] = i;
for(i = 1; i <= MAXN; ++i) for (j = i * 2; j <= MAXN; j += i) phi[j] -= phi[i];

#define MAXN 3000000
int phi[MAXN + 1], prime[MAXN/10], sz;
bitset <MAXN + 1> mark;

for (int i = 2; i <= MAXN; i++ ){
	if(!mark[i]){
		phi[i] = i-1;
		prime[sz++]= i;
	}
	for (int j=0; j<sz && prime[j]*i <= MAXN; j++ ){
		mark[prime[j]*i]=1;
		if(i%prime[j]==0){
			phi[i*prime[j]] = phi[i]*prime[j];
			break;
		}
		else phi[i*prime[j]] = phi[i]*(prime[j]-1 );
	}
}

int phi(int N)
{
	int x=N;
	for(int i=2; i*i<=N; i++)
	{
		if(N%i==0) x-=x/i;
		while(N%i==0) N/=i;
	}
	if(N>1) x-=x/N;
	return x;
}

//######################################################################################
//################################ TEORIA DE GRAFOS ####################################
//######################################################################################

//### MAX FLOW #########################################################################
int n;
int source, sink;
int capacity[200][200], residual[200][200];
int find_path()
{
	bool visited[n];
	memset(visited, 0, sizeof(visited));

	int from[n];
	memset(from, -1, sizeof(from));

	queue <int> Q;
	Q.push(source);
	visited[source] = 1;

	int where;

	while(!Q.empty())
	{
		where = Q.front();
		Q.pop();

		if(where==sink) break;

		for(int i=0; i<n; i++)
		{
			if(residual[where][i] > 0 && !visited[i])
			{
				Q.push(i);
				visited[i] = 1;
				from[i] = where;
			}
		}
	}
	int path_cap = 1<<30;
	where = sink;
	while(from[where] > -1)
	{
		int prev = from[where];
		path_cap = min(path_cap, residual[prev][where]);
		where = prev;
	}
	where = sink;
	while(from[where] > -1)
	{
		int prev = from[where];
		residual[prev][where] -= path_cap;
		residual[where][prev] += path_cap;
		where = prev;
	}
	if(path_cap == 1<<30) return 0;
	else return path_cap;
}
int max_flow()
{
	int flow = 0;
	while(1)
	{
		int path_cap = find_path();
		if(!path_cap) break;
		else flow += path_cap;
	}
	return flow;
}


//### BIPARTITE MATCHING - HOPCROFT-KARP O(E * sqrt(V)) ######################################################

// http://en.wikipedia.org/wiki/Hopcroft%E2%80%93Karp_algorithm
// http://www.spoj.pl/problems/MATCHING/
// http://acm.tju.edu.cn/toj/showp3783.html

#define MAXN 100000
#define INF (1<<28)

vector <int> adj[MAXN + 1]; // (u, v) <=> (v, u)
int n, m, NIL, match[MAXN + 1], dist[MAXN + 1];
// Izquierda; nodos del 0 al n-1
// Derecha: Nodos del n al n+m-1
// NIL: Nodo n+m

bool bfs(){
    queue <int> Q;
    for(int i=0; i<n; i++) {
        if(match[i] == NIL) {
            dist[i] = 0;
            Q.push(i);
        }
        else dist[i] = INF;
    }
    dist[NIL] = INF;

    while(!Q.empty()) {
        int u = Q.front(); Q.pop();
        for(int i=0; i<adj[u].size(); i++){
            int v = adj[u][i];
            if(dist[match[v]] == INF) {
                dist[match[v]] = dist[u] + 1;
                Q.push(match[v]);
            }
        }
    }
    return dist[NIL] != INF;
}

bool dfs(int u) {
	if(u != NIL) {
		for(int i=0; i<adj[u].size(); i++) {
			int v = adj[u][i];
			if(dist[match[v]] == dist[u] + 1) {
				if(dfs(match[v])) {
					match[v] = u;
					match[u] = v;
					return true;
				}
			}
		}
		dist[u] = INF;
		return false;
	}
	return true;
}

int hopcroft_karp()
{
    NIL = n + m;
    for(int i=0; i<n+m; i++)
    	match[i] = NIL;

    int matching = 0;

    //Greedy Step
    for(int u=0; u<n; u++)
    {
    	for(int i=0; i<adj[u].size(); i++)
    	{
    		int v = adj[u][i];
    		if(match[v] == NIL)
    		{
    			matching++;
    			match[u] = v;
    			match[v] = u;
    			break;
    		}
    	}
    }

    while(bfs())
        for(int u=0; u<n; u++)
            if(match[u] == NIL && dfs(u))
                matching++;

    return matching;
}

//### NON BIPARTITE MATCHING #####################################################################

#define MAXN 222

int n;
bool adj[MAXN][MAXN];
int p[MAXN];
int m[MAXN];
int d[MAXN];
int c1[MAXN], c2[MAXN];
int q[MAXN], *qf, *qb;

int pp[MAXN];
int f(int x) {return x == pp[x] ? x : (pp[x] = f(pp[x]));}
void u(int x, int y) {pp[f(x)] = f(y);}

int v[MAXN];

void path(int r, int x)
{
    if (r == x) return;

    if (d[x] == 0)
    {
        path(r, p[p[x]]);
        int i = p[x], j = p[p[x]];
        m[i] = j; m[j] = i;
    }
    else if (d[x] == 1)
    {
        path(m[x], c1[x]);
        path(r, c2[x]);
        int i = c1[x], j = c2[x];
        m[i] = j; m[j] = i;
    }
}

int lca(int x, int y, int r)
{
    int i = f(x), j = f(y);
    while (i != j && v[i] != 2 && v[j] != 1)
    {
        v[i] = 1; v[j] = 2;
        if (i != r) i = f(p[i]);
        if (j != r) j = f(p[j]);
    }

    int b = i, z = j;
    if(v[j] == 1) swap(b, z);

    for (i = b; i != z; i = f(p[i])) v[i] = -1;
    v[z] = -1;
    return b;
}

void shrink_one_side(int x, int y, int b)
{
    for(int i = f(x); i != b; i = f(p[i]))
    {
        u(i, b);
        if(d[i] == 1) c1[i] = x, c2[i] = y, *qb++ = i;
    }
}

bool BFS(int r)
{
    for(int i=0; i<n; ++i)
    	pp[i] = i;

    memset(v, -1, sizeof(v));
    memset(d, -1, sizeof(d));

    d[r] = 0;

    qf = qb = q;
    *qb++ = r;

    while(qf < qb)
    {
        for(int x=*qf++, y=0; y<n; ++y)
        {
            if(adj[x][y] && m[y] != y && f(x) != f(y))
            {
                if(d[y] == -1)
                {
                    if(m[y] == -1)
                    {
						path(r, x);
						m[x] = y; m[y] = x;
						return true;
                    }
                    else
                    {
						p[y] = x; p[m[y]] = y;
						d[y] = 1; d[m[y]] = 0;
						*qb++ = m[y];
                    }
                }
                else if(d[f(y)] == 0)
                {
					int b = lca(x, y, r);
					shrink_one_side(x, y, b);
					shrink_one_side(y, x, b);
                }
        	}
		}
	}

    return false;
}

int match()
{
    memset(m, -1, sizeof(m));

    int c = 0;
    for (int i=0; i<n; ++i)
        if (m[i] == -1)
            if (BFS(i)) c++;
            else m[i] = i;

    return c;
}

//######################################################################################
//###################################### BIG NUMS ######################################
//######################################################################################

//### SUMA DE CADENAS ##################################################################
string suma(const string &a, const string &b)
{
	int LA = a.size(), LB = b.size(), L = max(LA, LB), carry = 0;

    string x = string(L, '0');

    while(L--)
    {
    	LA--; LB--;

        if(LA >= 0) carry += a[LA] - '0';
        if(LB >= 0) carry += b[LB] - '0';

        if(carry < 10) x[L] = '0' + carry, carry = 0;
        else x[L] = '0' + carry - 10, carry = 1;
    }

    if(carry) x = '1' + x;
    return x;
}


//### PRODUCTO DE CADENAS ##################################################################
string prod(string a, string b)
{
	if(a=="0" || b=="0") return "0";
	else if(a.size()==1)
	{
		int m = a[0] - '0';

		string ans = string(b.size(), '0');

		int lleva = 0;

		for(int i=b.size()-1; i>=0; i--)
		{
			int d = (b[i] - '0') * m + lleva;
			lleva = d/10;
			ans[i] += d%10;
		}
		if(lleva) ans = (char)(lleva + '0') + ans;
		return ans;
	}
	else if(b.size()==1) return prod(b, a);
	else
	{
		string ans = "0";
		string ceros = "";
		for(int i=a.size()-1; i>=0; i--)
		{
			string s = prod(string(1, a[i]), b) + ceros;
			ceros += "0";
			ans = suma(ans, s);
		}
		return ans;
	}
}

//######################################################################################
//############################# GEOMETRIA COMPUTACIONAL ################################
//######################################################################################

#define EPS 1e-8
#define PI acos(-1)
#define Vector Point

struct Point
{
    double x, y;
    Point(){}
    Point(double a, double b) { x = a; y = b; }
    double mod2() { return x*x + y*y; }
    double mod()  { return sqrt(x*x + y*y); }
    double arg()  { return atan2(y, x); }
    Point ort()   { return Point(-y, x); }
    Point unit()  { double k = mod(); return Point(x/k, y/k); }
};

Point operator +(const Point &a, const Point &b) { return Point(a.x + b.x, a.y + b.y); }
Point operator -(const Point &a, const Point &b) { return Point(a.x - b.x, a.y - b.y); }
Point operator /(const Point &a, double k) { return Point(a.x/k, a.y/k); }
Point operator *(const Point &a, double k) { return Point(a.x*k, a.y*k); }

bool operator ==(const Point &a, const Point &b)
{
    return abs(a.x - b.x) < EPS && abs(a.y - b.y) < EPS;
}
bool operator !=(const Point &a, const Point &b)
{
    return !(a==b);
}
bool operator <(const Point &a, const Point &b)
{
    if(abs(a.x - b.x) > EPS) return a.x < b.x;
    return a.y + EPS < b.y;
}

//### FUNCIONES BASICAS #############################################################

double dist(const Point &A, const Point &B)    { return hypot(A.x - B.x, A.y - B.y); }
double cross(const Vector &A, const Vector &B) { return A.x * B.y - A.y * B.x; }
double dot(const Vector &A, const Vector &B)   { return A.x * B.x + A.y * B.y; }
double area(const Point &A, const Point &B, const Point &C) { return cross(B - A, C - A); }

// Heron triangulo y cuadrilatero ciclico
// http://mathworld.wolfram.com/CyclicQuadrilateral.html
// http://www.spoj.pl/problems/QUADAREA/

double areaHeron(double a, double b, double c)
{
	double s = (a + b + c) / 2;
	return sqrt(s * (s-a) * (s-b) * (s-c));
}

double circumradius(double a, double b, double c) { return a * b * c / (4 * areaHeron(a, b, c)); }

double areaHeron(double a, double b, double c, double d)
{
	double s = (a + b + c + d) / 2;
	return sqrt((s-a) * (s-b) * (s-c) * (s-d));
}

double circumradius(double a, double b, double c, double d) { return sqrt((a*b + c*d) * (a*c + b*d) * (a*d + b*c))  / (4 * areaHeron(a, b, c, d)); }

//### DETERMINA SI P PERTENECE AL SEGMENTO AB ###########################################
bool between(const Point &A, const Point &B, const Point &P)
{
    return  P.x + EPS >= min(A.x, B.x) && P.x <= max(A.x, B.x) + EPS &&
            P.y + EPS >= min(A.y, B.y) && P.y <= max(A.y, B.y) + EPS;
}

bool onSegment(const Point &A, const Point &B, const Point &P)
{
    return abs(area(A, B, P)) < EPS && between(A, B, P);
}

//### DETERMINA SI EL SEGMENTO P1Q1 SE INTERSECTA CON EL SEGMENTO P2Q2 #####################
//funciona para cualquiera P1, P2, P3, P4
bool intersects(const Point &P1, const Point &P2, const Point &P3, const Point &P4)
{
    double A1 = area(P3, P4, P1);
    double A2 = area(P3, P4, P2);
    double A3 = area(P1, P2, P3);
    double A4 = area(P1, P2, P4);

    if( ((A1 > 0 && A2 < 0) || (A1 < 0 && A2 > 0)) &&
        ((A3 > 0 && A4 < 0) || (A3 < 0 && A4 > 0)))
            return true;

    else if(A1 == 0 && onSegment(P3, P4, P1)) return true;
    else if(A2 == 0 && onSegment(P3, P4, P2)) return true;
    else if(A3 == 0 && onSegment(P1, P2, P3)) return true;
    else if(A4 == 0 && onSegment(P1, P2, P4)) return true;
    else return false;
}

//### DETERMINA SI A, B, M, N PERTENECEN A LA MISMA RECTA ##############################
bool sameLine(Point P1, Point P2, Point P3, Point P4)
{
	return area(P1, P2, P3) == 0 && area(P1, P2, P4) == 0;
}
//### SI DOS SEGMENTOS O RECTAS SON PARALELOS ###################################################
bool isParallel(const Point &P1, const Point &P2, const Point &P3, const Point &P4)
{
	return cross(P2 - P1, P4 - P3) == 0;
}

//### PUNTO DE INTERSECCION DE DOS RECTAS NO PARALELAS #################################
Point lineIntersection(const Point &A, const Point &B, const Point &C, const Point &D)
{
    return A + (B - A) * (cross(C - A, D - C) / cross(B - A, D - C));
}

Point circumcenter(const Point &A, const Point &B, const Point &C)
{
	return (A + B + (A - B).ort() * dot(C - B, A - C) / cross(A - B, A - C)) / 2;
}

//### FUNCIONES BASICAS DE POLIGONOS ################################################
bool isConvex(const vector <Point> &P)
{
    int n = P.size(), pos = 0, neg = 0;
    for(int i=0; i<n; i++)
    {
        double A = area(P[i], P[(i+1)%n], P[(i+2)%n]);
        if(A < 0) neg++;
        else if(A > 0) pos++;
    }
    return neg == 0 || pos == 0;
}

double area(const vector <Point> &P)
{
    int n = P.size();
    double A = 0;
    for(int i=1; i<=n-2; i++)
        A += area(P[0], P[i], P[i+1]);
    return abs(A/2);
}

bool pointInPoly(const vector <Point> &P, const Point &A)
{
    int n = P.size(), cnt = 0;
    for(int i=0; i<n; i++)
    {
        int inf = i, sup = (i+1)%n;
        if(P[inf].y > P[sup].y) swap(inf, sup);
        if(P[inf].y <= A.y && A.y < P[sup].y)
            if(area(A, P[inf], P[sup]) > 0)
                cnt++;
    }
    return (cnt % 2) == 1;
}

//### CONVEX HULL ######################################################################
// O(nh)
vector <Point> ConvexHull(vector <Point> S)
{
	sort(all(S));

	int it=0;
	Point primero = S[it], ultimo =  primero;

	int n = S.size();

	vector <Point> convex;
	do
	{
		convex.push_back(S[it]);
		it = (it + 1)%n;

		for(int i=0; i<S.size(); i++)
		{
			if(S[i]!=ultimo && S[i]!=S[it])
			{
				if(area(ultimo, S[it], S[i]) < EPS) it = i;
			}
		}

		ultimo=S[it];
	}while(ultimo!=primero);

	return convex;
}

// O(n log n)
vector <Point> ConvexHull(vector <Point> P)
{
    sort(P.begin(),P.end());
    int n = P.size(),k = 0;
    Point H[2*n];

    for(int i=0;i<n;++i){
        while(k>=2 && area(H[k-2],H[k-1],P[i]) <= 0) --k;
        H[k++] = P[i];
    }

    for(int i=n-2,t=k;i>=0;--i){
        while(k>t && area(H[k-2],H[k-1],P[i]) <= 0) --k;
        H[k++] = P[i];
    }

    return vector <Point> (H,H+k-1);
}

//### DETERMINA SI P ESTA EN EL INTERIOR DEL POLIGONO CONVEXO A ########################

// O (log n)
bool isInConvex(vector <Point> &A, const Point &P)
{
	int n = A.size(), lo = 1, hi = A.size() - 1;

	if(area(A[0], A[1], P) <= 0) return 0;
	if(area(A[n-1], A[0], P) <= 0) return 0;

	while(hi - lo > 1)
	{
		int mid = (lo + hi) / 2;

		if(area(A[0], A[mid], P) > 0) lo = mid;
		else hi = mid;
	}

	return area(A[lo], A[hi], P) > 0;
}

// O(n)
Point norm(const Point &A, const Point &O)
{
    Vector V = A - O;
    V = V * 10000000000.0 / V.mod();
    return O + V;
}

bool isInConvex(vector <Point> &A, vector <Point> &B)
{
    if(!isInConvex(A, B[0])) return 0;
    else
    {
        int n = A.size(), p = 0;

        for(int i=1; i<B.size(); i++)
        {
            while(!intersects(A[p], A[(p+1)%n], norm(B[i], B[0]), B[0])) p = (p+1)%n;

            if(area(A[p], A[(p+1)%n], B[i]) <= 0) return 0;
        }

        return 1;
    }
}

//##### SMALLEST ENCLOSING CIRCLE O(n) ###############################################
// http://www.cs.uu.nl/docs/vakken/ga/slides4b.pdf
// http://www.spoj.pl/problems/ALIENS/

pair <Point, double> enclosingCircle(vector <Point> P)
{
    random_shuffle(P.begin(), P.end());

    Point O(0, 0);
    double R2 = 0;

    for(int i=0; i<P.size(); i++)
    {
        if((P[i] - O).mod2() > R2 + EPS)
        {
            O = P[i], R2 = 0;
            for(int j=0; j<i; j++)
            {
                if((P[j] - O).mod2() > R2 + EPS)
                {
                    O = (P[i] + P[j])/2, R2 = (P[i] - P[j]).mod2() / 4;
                    for(int k=0; k<j; k++)
                        if((P[k] - O).mod2() > R2 + EPS)
                            O = circumcenter(P[i], P[j], P[k]), R2 = (P[k] - O).mod2();
                }
            }
        }
    }
    return make_pair(O, sqrt(R2));
}

//##### CLOSEST PAIR OF POINTS ########################################################
bool XYorder(Point P1, Point P2)
{
	if(P1.x != P2.x) return P1.x < P2.x;
	return P1.y < P2.y;
}
bool YXorder(Point P1, Point P2)
{
	if(P1.y != P2.y) return P1.y < P2.y;
	return P1.x < P2.x;
}
double closest_recursive(vector <Point> vx, vector <Point> vy)
{
	if(vx.size()==1) return 1e20;
	if(vx.size()==2) return dist(vx[0], vx[1]);

	Point cut = vx[vx.size()/2];

	vector <Point> vxL, vxR;
	for(int i=0; i<vx.size(); i++)
		if(vx[i].x < cut.x || (vx[i].x == cut.x && vx[i].y <= cut.y))
			vxL.push_back(vx[i]);
		else vxR.push_back(vx[i]);

	vector <Point> vyL, vyR;
	for(int i=0; i<vy.size(); i++)
		if(vy[i].x < cut.x || (vy[i].x == cut.x && vy[i].y <= cut.y))
			vyL.push_back(vy[i]);
		else vyR.push_back(vy[i]);

	double dL = closest_recursive(vxL, vyL);
	double dR = closest_recursive(vxR, vyR);
	double d = min(dL, dR);

	vector <Point> b;
	for(int i=0; i<vy.size(); i++)
		if(abs(vy[i].x - cut.x) <= d)
			b.push_back(vy[i]);

	for(int i=0; i<b.size(); i++)
		for(int j=i+1; j<b.size() && (b[j].y - b[i].y) <= d; j++)
			d = min(d, dist(b[i], b[j]));

	return d;
}
double closest(vector <Point> points)
{
	vector <Point> vx = points, vy = points;
	sort(vx.begin(), vx.end(), XYorder);
	sort(vy.begin(), vy.end(), YXorder);

	for(int i=0; i+1<vx.size(); i++)
		if(vx[i] == vx[i+1])
			return 0.0;

	return closest_recursive(vx,vy);
}

// INTERSECCION DE CIRCULOS
vector <Point> circleCircleIntersection(Point O1, double r1, Point O2, double r2)
{
	vector <Point> X;

	double d = dist(O1, O2);

	if(d > r1 + r2 || d < max(r2, r1) - min(r2, r1)) return X;
	else
	{
		double a = (r1*r1 - r2*r2 + d*d) / (2.0*d);
		double b = d - a;
		double c = sqrt(abs(r1*r1 - a*a));

		Vector V = (O2-O1).unit();
		Point H = O1 + V * a;

		X.push_back(H + V.ort() * c);

		if(c > EPS) X.push_back(H - V.ort() * c);
	}

	return X;
}

// LINEA AB vs CIRCULO (O, r)
// 1. Mucha perdida de precision, reemplazar por resultados de formula.
// 2. Considerar line o segment

vector <Point> lineCircleIntersection(Point A, Point B, Point O, long double r)
{
	vector <Point> X;

	Point H1 = O + (B - A).ort() * cross(O - A, B - A) / (B - A).mod2();
	long double d2 = cross(O - A, B - A) * cross(O - A, B - A) / (B - A).mod2();

	if(d2 <= r*r + EPS)
	{
		long double k = sqrt(abs(r * r - d2));

		Point P1 = H1 + (B - A) * k / (B - A).mod();
		Point P2 = H1 - (B - A) * k / (B - A).mod();

		if(between(A, B, P1)) X.push_back(P1);

		if(k > EPS && between(A, B, P2)) X.push_back(P2);
	}

	return X;
}

//### PROBLEMAS BASICOS ###############################################################
void CircumscribedCircle()
{
	int x1, y1, x2, y2, x3, y3;
	scanf("%d %d %d %d %d %d", &x1, &y1, &x2, &y2, &x3, &y3);

	Point A(x1, y1), B(x2, y2), C(x3, y3);

	Point P1 = (A + B) / 2.0;
	Point P2 = P1 + (B-A).ort();
	Point P3 = (A + C) / 2.0;
	Point P4 = P3 + (C-A).ort();

	Point CC = lineIntersection(P1, P2, P3, P4);
	double r = dist(A, CC);

	printf("(%.6lf,%.6lf,%.6lf)\n", CC.x, CC.y, r);
}

void InscribedCircle()
{
	int x1, y1, x2, y2, x3, y3;
	scanf("%d %d %d %d %d %d", &x1, &y1, &x2, &y2, &x3, &y3);

	Point A(x1, y1), B(x2, y2), C(x3, y3);

	Point AX = A + (B-A).unit() + (C-A).unit();
	Point BX = B + (A-B).unit() + (C-B).unit();

	Point CC = lineIntersection(A, AX, B, BX);
	double r = abs(area(A, B, CC) / dist(A, B));

	printf("(%.6lf,%.6lf,%.6lf)\n", CC.x, CC.y, r);
}

vector <Point>  TangentLineThroughPoint(Point P, Point C, long double r)
{
	vector <Point> X;

	long double h2 = (C - P).mod2();
	if(h2 < r*r) return X;
	else
	{
		long double d = sqrt(h2 - r*r);

		long double m1 = (r*(P.x - C.x) + d*(P.y - C.y)) / h2;
		long double n1 = (P.y - C.y - d*m1) / r;

		long double n2 = (d*(P.x - C.x) + r*(P.y - C.y)) / h2;
		long double m2 = (P.x - C.x - d*n2) / r;

		X.push_back(C + Point(m1, n1)*r);
		if(d != 0) X.push_back(C + Point(m2, n2)*r);

		return X;
	}
}

void TangentLineThroughPoint()
{
	int xc, yc, r, xp, yp;
	scanf("%d %d %d %d %d", &xc, &yc, &r, &xp, &yp);

	Point C(xc, yc), P(xp, yp);

	double hyp = dist(C, P);
	if(hyp < r) printf("[]\n");
	else
	{
		double d = sqrt(hyp * hyp - r*r);

		double m1 = (r*(P.x - C.x) + d*(P.y - C.y)) / (r*r + d*d);
		double n1 = (P.y - C.y - d*m1) / r;
		double ang1 = 180 * atan(-m1/n1) / PI + EPS;
		if(ang1 < 0) ang1 += 180.0;

		double n2 = (d*(P.x - C.x) + r*(P.y - C.y)) / (r*r + d*d);
		double m2 = (P.x - C.x - d*n2) / r;
		double ang2 = 180 * atan(-m2/n2) / PI + EPS;
		if(ang2 < 0) ang2 += 180.0;

		if(ang1 > ang2) swap(ang1, ang2);

		if(d == 0) printf("[%.6lf]\n", ang1);
		else printf("[%.6lf,%.6lf]\n", ang1, ang2);
	}
}

void CircleThroughAPointAndTangentToALineWithRadius()
{
	int xp, yp, x1, y1, x2, y2, r;
	scanf("%d %d %d %d %d %d %d", &xp, &yp, &x1, &y1, &x2, &y2, &r);

	Point P(xp, yp), A(x1, y1), B(x2, y2);

	Vector V = (B - A).ort() * r / (B - A).mod();

	Point X[2];
	int cnt = 0;

	Point H1 = P + (B - A).ort() * cross(P - A, B - A) / (B - A).mod2() + V;
	double d1 = abs(r + cross(P - A, B - A) / (B - A).mod());

	if(d1 - EPS <= r)
	{
		double k = sqrt(abs(r * r - d1 * d1));

		X[cnt++] = Point(H1 + (B - A).unit() * k);

		if(k > EPS) X[cnt++] = Point(H1 - (B - A).unit() * k);
	}

	Point H2 = P + (B - A).ort() * cross(P - A, B - A) / (B - A).mod2() - V;
	double d2 = abs(r - cross(P - A, B - A) / (B - A).mod());

	if(d2 - EPS <= r)
	{
		double k = sqrt(abs(r * r - d2 * d2));

		X[cnt++] = Point(H2 + (B - A).unit() * k);

		if(k > EPS) X[cnt++] = Point(H2 - (B - A).unit() * k);
	}

	sort(X, X + cnt);

	if(cnt == 0) printf("[]\n");
	else if(cnt == 1) printf("[(%.6lf,%.6lf)]\n", X[0].x, X[0].y);
	else if(cnt == 2) printf("[(%.6lf,%.6lf),(%.6lf,%.6lf)]\n", X[0].x, X[0].y, X[1].x, X[1].y);
}

void CircleTangentToTwoLinesWithRadius()
{
	int x1, y1, x2, y2, x3, y3, x4, y4, r;
	scanf("%d %d %d %d %d %d %d %d %d", &x1, &y1, &x2, &y2, &x3, &y3, &x4, &y4, &r);

	Point A1(x1, y1), B1(x2, y2), A2(x3, y3), B2(x4, y4);

	Vector V1 = (B1 - A1).ort() * r / (B1 - A1).mod();
	Vector V2 = (B2 - A2).ort() * r / (B2 - A2).mod();

	Point X[4];
	X[0] = lineIntersection(A1 + V1, B1 + V1, A2 + V2, B2 + V2);
	X[1] = lineIntersection(A1 + V1, B1 + V1, A2 - V2, B2 - V2);
	X[2] = lineIntersection(A1 - V1, B1 - V1, A2 + V2, B2 + V2);
	X[3] = lineIntersection(A1 - V1, B1 - V1, A2 - V2, B2 - V2);

	sort(X, X + 4);
	printf("[(%.6lf,%.6lf),(%.6lf,%.6lf),(%.6lf,%.6lf),(%.6lf,%.6lf)]\n", X[0].x, X[0].y, X[1].x, X[1].y, X[2].x, X[2].y, X[3].x, X[3].y);
}

void CircleTangentToTwoDisjointCirclesWithRadius()
{
	int x1, y1, r1, x2, y2, r2, r;
	scanf("%d %d %d %d %d %d %d", &x1, &y1, &r1, &x2, &y2, &r2, &r);

	Point A(x1, y1), B(x2, y2);

	r1 += r;
	r2 += r;

	double d = dist(A, B);

	if(d > r1 + r2 || d < max(r1, r2) - min(r1, r2)) printf("[]\n");
	else
	{
		double a = (r1*r1 - r2*r2 + d*d) / (2.0*d);
		double b = d - a;
		double c = sqrt(abs(r1*r1 - a*a));

		Vector V = (B-A).unit();
		Point H = A + V * a;

		Point P1 = H + V.ort() * c;
		Point P2 = H - V.ort() * c;

		if(P2 < P1) swap(P1, P2);

		if(P1 == P2) printf("[(%.6lf,%.6lf)]\n", P1.x, P1.y);
		else printf("[(%.6lf,%.6lf),(%.6lf,%.6lf)]\n", P1.x, P1.y, P2.x, P2.y);
	}
}

//######################################################################################
//############################# STRING SEARCHING #######################################
//######################################################################################

//### KNUTH MORRIS PRATT ################################################################
vector <int> KMP(string T, string P)
{
    vector <int> B(P.size() + 1, -1);
    for(int i = 0, j = -1; i < P.size(); i++)
    {
        while(j != -1 && P[i] != P[j]) j = B[j];
        j++;
        B[i + 1] = j;
    }

    vector <int> matches;
    for(int i = 0, j = 0; i < T.size(); i++)
    {
        while(j != -1 && T[i] != P[j]) j = B[j];
        j++;
        if(j == P.size()) matches.push_back(i + 1 - j), j = B[j];
    }

    return matches;
}

//### Suffix Array O(nlogn) ################################################################
//http://www.spoj.pl/problems/SARRAY/
//http://www.spoj.pl/problems/SUBST1/

#define checkMod(i, n) (((i) < (n)) ? (i) : (i) - (n))
#define MAXN 1000000
#define ALPH_SIZE 256

using namespace std;

char s[MAXN + 5];
int n;

int p[MAXN + 1], lcp[MAXN + 1], cnt[MAXN + 1], c[MAXN + 1];
int pn[MAXN + 1], cn[MAXN + 1];

void build_suffix_array()
{
	memset(cnt, 0, ALPH_SIZE * sizeof(int));
	for(int i=0; i<n; ++i) ++cnt[s[i]];
	for(int i=1; i<ALPH_SIZE; ++i) cnt[i] += cnt[i-1];
	for(int i=0; i<n; ++i) p[--cnt[s[i]]] = i;

	c[p[0]] = 0;
	int classes = 1;
	for(int i=1; i<n; ++i){
		if(s[p[i]] != s[p[i-1]]) ++classes;
		c[p[i]] = classes-1;
	}

	for(int h=0; (1<<h)<n; ++h){
		for(int i=0; i<n; ++i) pn[i] = checkMod(p[i] - (1<<h) + n, n);

		memset(cnt, 0, classes * sizeof(int));
		for(int i=0; i<n; ++i) ++cnt[c[pn[i]]];
		for(int i=1; i<classes; ++i) cnt[i] += cnt[i-1];
		for(int i=n-1; i>=0; i--) p[--cnt[c[pn[i]]]] = pn[i];

		for(int i=0; i<n; ++i) pn[i] = checkMod(p[i] + (1<<h), n);

		cn[p[0]] = 0;
		classes = 1;
		for(int i=1; i<n; ++i){
			if(c[p[i]] != c[p[i-1]] || c[pn[i]] != c[pn[i-1]]) ++classes;
			cn[p[i]] = classes-1;
		}
		memcpy(c, cn, n * sizeof(int));
	}
}

void build_lcp() {
	int k = 0;
	for(int i = 0; i < n; i++) if (c[i]) {
		int j = p[c[i] - 1];
		while(s[i + k] == s[j + k]) k++;
		lcp[c[i] - 1] = k;
		if (k) k--;
	}
	lcp[n - 1] = 0;
}

//### Suffix Automata O(n) ################################################################
//http://e-maxx.ru/algo/suffix_automata
//http://www.spoj.pl/problems/LCS/
//http://www.spoj.pl/problems/SUB_PROB/

#define MAXN 250005
#define ALPH_SIZE 26

using namespace std;

struct state{
	int len, link, next[ALPH_SIZE];
};

state st[MAXN*2];
int sz, last;

void sa_init() {
	sz = last = 0;
	st[0].len = 0;
	st[0].link = -1;
	++sz;
}

void sa_extend(char c){
	int cur = sz++;
	st[cur].len = st[last].len + 1;
	int p;
	for (p=last; p!=-1 && !st[p].next[c]; p=st[p].link)
		st[p].next[c] = cur;
	if (p == -1)
		st[cur].link = 0;
	else {
		int q = st[p].next[c];
		if (st[p].len + 1 == st[q].len)
			st[cur].link = q;
		else {
			int clone = sz++;
			st[clone].len = st[p].len + 1;
			memcpy(st[clone].next, st[q].next, ALPH_SIZE * sizeof(int));
			st[clone].link = st[q].link;
			for (; p!=-1 && st[p].next[c]==q; p=st[p].link)
				st[p].next[c] = clone;
			st[q].link = st[cur].link = clone;
		}
	}
	last = cur;
}

int lcs(char *s, char *t)
{
	sa_init();
	for(int i=0; s[i] != '\0'; i++)
		sa_extend(s[i] - 'a');

	int v = 0, l = 0, best = 0, bestpos = 0;
	for(int i=0; t[i] != '\0'; ++i){
		while (v && ! st[v].next[t[i] - 'a']) {
			v = st[v].link;
			l = st[v].len;
		}
		if (st[v].next[t[i] - 'a']) {
			v = st[v].next[t[i] - 'a'];
			++l;
		}
		if (l > best) best = l,  bestpos = i;
	}
	return best; // t.substr (bestpos-best+1, best);
}


//######################################################################################
//############################# TRIE ###############################################
//######################################################################################

//http://www.codechef.com/MAY12/problems/TWSTR/

#define MAXNODES 1005*1005
#define ALPH_SIZE 27

int nodes, trie[MAXNODES][ALPH_SIZE];

void init()
{
	nodes = 1;
	memset(trie, -1, sizeof(trie));
}

inline int enc(char ch)
{
	if(ch == '-') return 26;
	else return ch - 'a';
}

void insert(string &s)
{
	int p = 0;
	for(int i=0; i<s.size(); i++)
	{
		if(trie[p][enc(s[i])] == -1) trie[p][enc(s[i])] = nodes++;
		p = trie[p][enc(s[i])];
	}
}

bool find(string &s)
{
	int p = 0;
	for(int i=0; i<s.size(); i++)
	{
		if(trie[p][enc(s[i])] == -1) return 0;
		p = trie[p][enc(s[i])];
	}
	return 1;
}


//######################################################################################
//############################# MATRICES ###############################################
//######################################################################################

#define MOD 1000000007
#define SIZE 16

struct Matrix
{
	int X[SIZE][SIZE];

	Matrix () {}
	Matrix (int k)
	{
		memset(X, 0, sizeof(X));

		for(int i=0; i<SIZE; i++)
			X[i][i] = k;
	}
};

Matrix operator *(Matrix &A, Matrix &B)
{
	Matrix M;

	for(int i=0; i<SIZE; i++)
	{
		for(int j=0; j<SIZE; j++)
		{
			long long tmp = 0;
			for(int k=0; k<SIZE; k++)
				tmp += (long long)A.X[i][k] * B.X[k][j];
			M.X[i][j] = tmp % MOD;
		}
	}

	return M;
}

Matrix pow(Matrix x, long long n)
{
	Matrix P(1);

	while(n)
	{
		if(n & 1) P = P * x;

		n >>= 1;
		x = x * x;
	}

	return P;
}


long long modpow(long long x, long long n)
{
	long long P = 1;

	while(n)
	{
		if(n & 1) P = P * x % MOD;

		n >>= 1;
		x = x * x % MOD;
	}

	return P;
}

// ##########################################################################
// Miller-Rabin (n impar > 3)
// http://projecteuler.net/problem=216

long long modprod(long long A, long long B, long long MOD)
{
	long long P = 0;

	while(B)
	{
		if(B & 1) P = (P + A) % MOD;

		B >>= 1;
		A = (A << 1) % MOD;
	}
	return P;
}

long long modpow(long long x, long long n, long long MOD)
{
    long long P = 1;

    while(n)
    {
        if(n & 1) P = modprod(P, x, MOD);

        n >>= 1;
        x = modprod(x, x, MOD);
    }

    return P;
}

bool isProbablePrime(long long n)
{
	long long m = n - 1; int k = 0;
	while((m & 1) == 0) k++, m >>= 1;

	for(int it=0; it<5; it++)
	{
		long long a = 2 + rand() % (n - 3), x = modpow(a, m, n);
		if(x != 1 && x != n-1)
		{
			bool probablePrime = 0;

			for(int r=1; r<k && !probablePrime; r++)
			{
				x = modprod(x, x, n);
				if(x == 1) return 0;
				if(x == n - 1) probablePrime = 1;
			}

			if(!probablePrime) return 0;
		}
	}

	return 1;
}

//######################################################################################
//############################# BIT ####################################################
//######################################################################################

#define MAXN 1000000

int n, t[MAXN + 1], v[MAXN + 1];

int sum(int x)
{
	int result = 0;
	for(int i = x; i >= 0; i = (i & (i+1)) - 1)
		result += t[i];
	return result;
}

void inc(int x, int delta)
{
    v[x] += delta;
	for(int i = x; i < n; i = (i | (i+1)))
		t[i] += delta;
}

//######################################################################################
//############################# Segment Tree - Lazy Propragation #######################
//######################################################################################

// http://www.codeforces.com/contest/240/problem/F

// *** TODOS los intervalos son [cerrado,abierto> ***

#define MAXN 100000

struct node
{
	char flag;
	int cnt[26];
};
node operator +(const node &L, const node &R)
{
	node ans;
	ans.flag = 0;
	for(int i=0; i<26; i++)
		ans.cnt[i] = L.cnt[i] + R.cnt[i];
	return ans;
}

struct SegmentTree
{
	node T[4 * MAXN], NEUTRAL;

	char s[MAXN + 1];

	SegmentTree()
	{
		NEUTRAL.flag = 0;
		memset(NEUTRAL.cnt, 0, sizeof(NEUTRAL.cnt));
	}

	inline void push(int x, int b, int e)
	{
		if(T[x].flag)
		{
			memset(T[x].cnt, 0, sizeof(T[x].cnt));
			T[x].cnt[T[x].flag - 'a'] = e - b;

			int L = x + x + 1, R = L + 1;
			if(b + 1 == e) s[b] = T[x].flag;
			else T[L].flag = T[R].flag = T[x].flag;
			T[x].flag = 0;
		}
	}

	void init(int x, int b, int e)
	{
		if(b + 1 == e) T[x].cnt[s[b] - 'a'] = 1;
		else
		{
			int m = (b + e) >> 1, L = x + x + 1, R = L + 1;
			init(L, b, m);
			init(R, m, e);
			T[x] = T[L] + T[R];
		}
	}

	node query(int x, int b, int e, int i, int j)
	{
		push(x, b, e);

		if(j <= b || e <= i) return NEUTRAL;
		if(i <= b && e <= j) return T[x];

		int m = (b + e) >> 1, L = x + x + 1, R = L + 1;
		return query(L, b, m, i, j) + query(R, m, e, i, j);
	}

	void update(int x, int b, int e, int i, int j, char ch)
	{
		if(i <= b && e <= j)
		{
			T[x].flag = ch;
			push(x, b, e);
			return;
		}

		push(x, b, e);

		if(j <= b || e <= i) return;

		int m = (b + e) >> 1, L = x + x + 1, R = L + 1;
		update(L, b, m, i, j, ch);
		update(R, m, e, i, j, ch);
		T[x] = T[L] + T[R];
	}

	void print(int x, int b, int e)
	{
		push(x, b, e);
		if(b + 1 == e) printf("%c", s[b]);
		else
		{
			int m = (b + e) >> 1, L = x + x + 1, R = L + 1;
			print(L, b, m);
			print(R, m, e);
		}
	}
};

SegmentTree ST;

//######################################################################################
//############################# Treap ##################################################
//######################################################################################

typedef struct node * pnode;

struct node{
	int x, y, cnt;
	//bool rev;
	pnode L, R;
	node() {}
	node(int x, int y): x(x), y(y), cnt(1), L(NULL), R(NULL) {}
};

pnode T;

inline int cnt(pnode &it){
	return it ? it->cnt : 0;
}

inline void upd_cnt(pnode &it){
	if(it){
		it->cnt = cnt(it->L) + cnt(it->R) + 1;
	}
}

// Lazy propagation
void push(pnode it){
	if (it && it->rev){
		it->rev = false;
		swap(it->L, it->R);
		if (it->L) it->L->rev ^= true;
		if (it->R) it->R->rev ^= true;
	}
}

// Split Treap
void split(pnode t, int x, pnode &L, pnode &R){
	if (!t) L = R = NULL;
	else{
		//push(t);
		if (x < t->x)
			split (t->L, x, L, t->L), R = t;
		else
			split (t->R, x, t->R, R), L = t;
		upd_cnt(t);
	}
}

// Split Implicit Treap
void split(pnode t, pnode &L, pnode &R, int key){
	if (!t) L = R = NULL;
	else{
		//push(t);
		int cntL = cnt(t->L);
		if (key <= cntL)
			split (t->L, L, t->L, key), R = t;
		else
			split (t->R, t->R, R, key - cntL - 1), L = t;
		upd_cnt(t);
	}
}

// For Treap & Implicit Treap
void merge(pnode &t, pnode L, pnode R){
	//push(L);
	//push(R);
	if (!L) t = R;
	else if(!R) t = L;
	else if (L->y > R->y)
		merge (L->R, L->R, R), t = L;
	else
		merge (R->L, L, R->L), t = R;
	upd_cnt(t);
}

// Combines 2 treaps
pnode unite (pnode l, pnode r) {
	if (!l || !r) return l? l: r;
	if (l->y > r->y) swap (l, r);
	pnode lt, rt;
	split (r, l->x, lt, rt);
	l->L = unite(l->L, lt);
	l->R = unite(l->R, rt);
	return l;
}

// Find in Treap
bool find (pnode &t, int x) {
	if(!t) return 0;
	else if (t->x == x) return 1;
	else return find (x < t->x ? t->L: t->R, x);
}

// Erase from Treap
void erase (pnode &t, int x) {
    if(t) {
	   if (t-> x == x)
		  merge (t, t->L, t->R);
	   else
		  erase (x < t->x ? t->L: t->R, x);
	    upd_cnt(t);
    }
}

// Insert into Treap
void insert(pnode &t, pnode it) {
	if (!t) t = it;
	else if (it->y > t->y)
		split (t, it->x, it->L, it->R), t = it;
	else insert (it->x < t->x ? t->L: t->R, it);
	upd_cnt(t);
}

// Insert into Treap and return the # of greater elements
int insert(pnode &t, pnode it){
	int ret = 0;
	if (!t) t = it;
	else if (it->y > t->y)
		split (t, it->x, it->L, it->R), t = it, ret = cnt(t->R);
	else if(it->x < t->x)
		ret = 1 + cnt(t->R) + insert(t->L, it);
	else
		ret = insert(t->R, it);
	upd_cnt(t);
	return ret;
}

// Safely insert into Treap
void insert(int x)
{
	if(!find(T, x))
		insert(T, new node(x, rand()));
}

// Insert into implicit Treap
void insert(pnode &t, int value, int pos){
	pnode t1, t2;
	split(t, t1, t2, pos);
	merge(t1, t1, new node(value, rand()));
	merge(t, t1, t2);
}

// Reverse implicit Treap
void reverse(pnode &t, int l, int r){
	pnode t1, t2, t3;
	split(t, t1, t2, l);
	split(t2, t2, t3, r-l +1);
	t2->rev ^= true;
	merge(t, t1, t2);
	merge(t, t, t3);
}

//######################################################################################
//############################# SIMPLEX ################################################
//######################################################################################

#include <stdio.h>
#include <math.h>
#define  MMAX  25
#define  NMAX  25
#define  REAL  double
typedef REAL MAT[MMAX][NMAX];
MAT  A;
int  IPOSV[MMAX], IZROV[NMAX], i,j,ICASE,N,M,M1,M2,M3;
REAL R;
void simp1(MAT a,int mm,int *ll,int nll,int iabf,int *kp,REAL *bmax){
	int k;
	REAL test;
	*kp=ll[1];
	*bmax=a[mm+1][*kp+1];
	if(nll < 2) return;
	for(k=2; k<=nll; k++){
		if(iabf == 0) test=a[mm+1][ll[k]+1]-(*bmax);
		else test=fabs(a[mm+1][ll[k]+1])-fabs(*bmax);
		if(test > 0.0){
			*bmax=a[mm+1][ll[k]+1];
			*kp=ll[k];
		}
	}
}
void simp2(MAT a, int m,int n,int *l2,int nl2,int *ip,int kp,REAL *q1){
	REAL EPS=1e-6;
	int i,ii,k;
	REAL q,q0,qp;
	*ip=0;
	if(nl2 < 1) return;
	for(i=1; i<=nl2; i++)
		if(a[i+1][kp+1] < -EPS) goto e2;
	return;
	e2: *q1=-a[l2[i]+1][1]/a[l2[i]+1][kp+1];
	*ip=l2[i];
	if(i+1 > nl2) return;
	for(i=i+1; i<=nl2; i++){
		ii=l2[i];
		if(a[ii+1][kp+1] < -EPS){
			q=-a[ii+1][1]/a[ii+1][kp+1];
			if(q <  *q1){
				*ip=ii;
				*q1=q;
			}
			else if(q == *q1){
				for(k=1; k<=n; k++){
					qp=-a[*ip+1][k+1]/a[*ip+1][kp+1];
					q0=-a[ii+1][k+1]/a[ii+1][kp+1];
					if(q0 != qp) goto e6;
        		}
				e6: if(q0 < qp) *ip=ii;
			}
		}
	}
}
void simp3(MAT a,int i1,int k1,int ip,int kp){
	int ii,kk;
	REAL piv;
	piv=1.0/a[ip+1][kp+1];
	if(i1 >= 0)
		for(ii=1; ii<=i1+1; ii++)
			if(ii-1 != ip){
				a[ii][kp+1] *= piv;
				for(kk=1; kk<=k1+1; kk++)
					if(kk-1 != kp) a[ii][kk] -= a[ip+1][kk]*a[ii][kp+1];
			}
	for(kk=1; kk<=k1+1; kk++)
		if(kk-1 !=  kp) a[ip+1][kk] = -a[ip+1][kk]*piv;
	a[ip+1][kp+1]=piv;
}
void simplx(MAT a,int m,int n,int m1,int m2,int m3,int *icase,int *izrov, int *iposv){
	int i,ip,ir,is,k,kh,kp,m12,nl1,nl2,l1[NMAX],l2[MMAX],l3[MMAX];
	REAL bmax,q1,EPS=1e-6;
	if(m != m1+m2+m3) return; // Bad input constraint counts in simplx.
	nl1=n;
	for(k=1; k<=n; k++){
		l1[k]=k;
		izrov[k]=k;
	}
	nl2=m;
	for(i=1; i<=m; i++){
		if(a[i+1][1] < 0.0) return; // Constants bi must be nonnegative.
		l2[i]=i;
		iposv[i]=n+i;
	}
	for(i=1; i<=m2; i++) l3[i]=1;
	ir=0;
	if(m2+m3 == 0) goto e30;
	ir=1;
	for(k=1; k<=n+1; k++){
		q1=0.0;
		for(i=m1+1; i<=m; i++) q1 += a[i+1][k];
		a[m+2][k]=-q1;
	}
	e10: simp1(a,m+1,l1,nl1,0,&kp,&bmax);
	if(bmax <= EPS && a[m+2][1] < -EPS){
		*icase=-1;
		return;
	}
	else if(bmax <= EPS && a[m+2][1] <= EPS){
		m12=m1+m2+1;
		if(m12 <= m)
			for (ip=m12; ip<=m; ip++)
				if(iposv[ip] == ip+n){
					simp1(a,ip,l1,nl1,1,&kp,&bmax);
					if(bmax > EPS) goto e1;
				}
		ir=0;
		m12=m12-1;
		if(m1+1 > m12) goto e30;
		for (i=m1+1; i<=m1+m2; i++)
			if(l3[i-m1] == 1)
				for (k=1; k<=n+1; k++)
					a[i+1][k] *= -1.0;
		goto e30;
	}
	simp2(a,m,n,l2,nl2,&ip,kp,&q1);
	if(ip == 0){
		*icase=-1;
		return;
	}
	e1: simp3(a,m+1,n,ip,kp);
	if(iposv[ip] >= n+m1+m2+1){
		for(k=1; k<=nl1; k++)
			if(l1[k] == kp) goto e2;
		e2: nl1=nl1-1;
		for(is=k; is<=nl1; is++) l1[is]=l1[is+1];
	}
	else{
		if(iposv[ip] < n+m1+1) goto e20;
		kh=iposv[ip]-m1-n;
		if(l3[kh] == 0) goto e20;
		l3[kh]=0;
	}
	a[m+2][kp+1] += 1.0;
	for(i=1; i<=m+2; i++) a[i][kp+1] *= -1.0;
	e20: is=izrov[kp];
	izrov[kp]=iposv[ip];
	iposv[ip]=is;
	if(ir != 0) goto e10;
	e30: simp1(a,0,l1,nl1,0,&kp,&bmax);
	if(bmax <= EPS){
		*icase=0;
		return;
	}
	simp2(a,m,n,l2,nl2,&ip,kp,&q1);
	if(ip == 0){
		*icase=1;
		return;
	}
  simp3(a,m,n,ip,kp);
  goto e20;
}
int main()
{
	printf(" Number of variables in E.F.: "); scanf("%d", &N);
	printf(" Number of <= inequalities..: "); scanf("%d", &M1);
	printf(" Number of >= inequalities..: "); scanf("%d", &M2);
	printf(" Number of = equalities.....: "); scanf("%d", &M3);
	M = M1+M2+M3;
	for(i=1; i<=M+2; i++)
		for(j=1; j<=N+1; j++)
			A[i][j]=0.0;
	printf(" Input Economic Function:\n");
	for(i=2; i<=N+1; i++){
		printf(" Coefficient #%d: ", i-1); scanf("%lf", &A[1][i]);
	}
	printf(" Constant term : "); scanf("%lf", &A[1][1]);
	for(i=1; i<=M; i++){
		printf(" Input constraint #%d: \n", i);
		for(j=2; j<=N+1; j++){
			printf(" Coefficient #%d: ", j-1); scanf("%lf", &R);
			A[i+1][j] = -R;
		}
		printf(" Constant term : "); scanf("%lf", &A[i+1][1]);
	}
	printf("\n Input Table:\n");
	for(i=1; i<=M+1; i++){
		for (j=1; j<=N+1; j++)
			printf("%8.2f", A[i][j]);
		printf("\n");
	}
	simplx(A,M,N,M1,M2,M3,&ICASE,IZROV,IPOSV);
	if(ICASE==0){
		printf("\n Maximum of E.F. = %f\n", A[1][1]);
		for(i=1; i<=N; i++){
			for(j=1; j<=M; j++)
				if (IPOSV[j] == i){
					printf("  X%d = %f\n", i, A[j+1][1]);
					goto e3;
				}
			printf("  X%d = %f\n", i, 0.0);
			e3:;
		}
	}
	else printf(" No solution (error code = %d).\n", ICASE);
}
