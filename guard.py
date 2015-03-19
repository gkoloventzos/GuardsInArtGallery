#!/usr/bin/env python
"""
Project on Computational Geometry 2010.
Koloventzos Georgios
1115200400250
Finding the guards in a polygonian museum.
Compare with Chavatal's algorithm
"""
from CGAL import Point_2 as pu
from CGAL import *
from time import *
from math import *
from dcel import *
from random import *
from cgalvisual import *
from visual import scene, color

def combinations(iterable, r):
    # combinations('ABCD', 2) --> AB AC AD BC BD CD
    # combinations(range(4), 3) --> 012 013 023 123
    pool = tuple(iterable)
    n = len(pool)
    if r > n:
        return
    indices = range(r)
    yield tuple(pool[i] for i in indices)
    while True:
        for i in reversed(range(r)):
            if indices[i] != i + n - r:
                break
        else:
            return
        indices[i] += 1
        for j in range(i+1, r):
            indices[j] = indices[j-1] + 1
        yield tuple(pool[i] for i in indices)


def is_Point_2(o):
    return type(o) is Point_2
    
def is_Segment_2(o):
    return type(o) is Segment_2
    

################Constrained Library By Nikolaos Tzoumas#################
def acute_vertices(p):
    assert p.is_simple()
    len_p = len(p)
    orient = p.orientation()

    for i in xrange(len_p):
        o = orientation(p[i-1], p[i], p[(i+1)%len_p])
        if orient != o and o != Kernel.Sign.ZERO:
            yield i

def intersections(poly, x):
    """
    Generate all the intersections of
    polygon poly with x.
    """
    for edge in poly.edges:
        i = intersection(edge, x)
        if i:
            yield i

def sees(poly, i, j):
    assert i != j
    seg = Segment_2(poly[i], poly[j])
    vert = [poly[i], poly[j]]
    for e in poly.edges:
        p = intersection(seg, e)
        if is_Point_2(p) and p not in vert:
            return False
    return True


def is_tagent(poly, ray, acute_vertex_index):
    i = acute_vertex_index;
    p0 = poly[i]
    p1 = poly[i - 1]
    p2 = poly[(i+1)%len(poly)]
    p_projected = p0 + ray.to_vector()
    o1 = orientation(p_projected, p0, p1)
    o2 = orientation(p_projected, p0, p2)
    clinear = Kernel.Sign.ZERO
    return o1 == o2 or o1 == clinear or o2 == clinear
    
    

def critical_constrain_generators(poly):
    """
    Returns the pairs of indexes of vertices of the
    polygon that generate all critical constraints.
    The index of the acute vertice is always second
    in the pair.
    """
    for i in acute_vertices(p):
        for j in filter (lambda x: x!=i, xrange(len(p))):
            if sees(p, i, j) and is_tagent(p, Ray_2(p[j], p[i]), i):
                yield (j, i)


def squared_distance(p1, p2):
    return Segment_2(p1, p2).squared_length()

def shortest_segment(segments):
    shortst = segments[0]
    min_len = shortst.squared_length()
    for s in segments:
        if s.squared_length() < min_len:
            shortst = s
            min_len = shortst.squared_length()
    return shortst

def critical_constraints(poly):
        # for every critical constraint generating 
        # pair of vertices instantiate a ray from the
        # acute vertice and find out there the ray
        # intersects the polygon
        # (even tagent to a vertex, will do)
    for p_i, u_i in critical_constrain_generators(poly):
        ray_direction = Vector_2(poly[p_i], poly[u_i])
        ray = Ray_2(poly[u_i], poly[u_i] + ray_direction)
        cuts = filter(is_Point_2, intersections(poly, ray))

        # the start of the ray is obviously intersecting with poly
        # but we don't need that intersection
        cuts = filter(lambda p: p != poly[u_i], cuts)
        assert len(cuts) > 0
        #now yield the shortest constrain
        yield shortest_segment([Segment_2(poly[u_i], v) for v in cuts])

########################################################################

def clean_inter(a,b,p):
    """
    This finds if the intersection is clean meaning that
    it is not intersected in the start or the end of the segment
    """
    return not( p == a.start() or p == a.end() or\
           p == b.start() or p == b.end())


def betsearch(seq,list):
    """
    This is a better search if a Segment_2 is in a list
    as regular or opposite
    """
    for r in list:              
        if seq == r or seq.opposite() == r or is_Segment_2(intersection(seq,r)):
            return True
    return False
    
def seg_create(critical,perime,points):
    nncritical =[]
    while True:                 #find all segments inside the polygon
        for i in xrange(len(critical)):     #for all segments
            find_inter=False
            for j in xrange(i+1,len(critical)):
                l = intersection(critical[i],critical[j])
                if is_Point_2(l) and clean_inter(critical[i],critical[j],l):   #find if there is a clean intersection
                    crit1 = critical[i]
                    crit2 = critical[j]
                    critical.pop(i)
                    critical.pop(j-1)
                    critical.append(Segment_2(crit1[0],l))  #create the intersected segments
                    critical.append(Segment_2(l,crit1[1]))
                    critical.append(Segment_2(crit2[0],l))
                    critical.append(Segment_2(l,crit2[1]))
                    find_inter = True
                    points.append(l)
                    break
                elif is_Segment_2(l):
                    break
            if not find_inter:      #if there is not an intersection insert in new list
                o = critical[i]
                critical.pop(i)
                if not betsearch(o,nncritical) and not betsearch(o,perime):
                    nncritical.append(o)
            break
        if critical == []:
            break
    return nncritical

def slice_perimeter(polygon,ponbound):
    out=[]
    for e in polygon.edges:           #slice the polygon's perimeter
        import operator
        colinear=[]
        colinear.append(e.start())
        for t in ponbound:      #for every point in the onbound
            if e.has_on(t):     #if there is in this segment
                colinear.append(t)  #insert in the list
        colinear.append(e.end())
        colinear.sort()     #sort the list with x
        sc = sorted(colinear,key=operator.itemgetter(1))    #sort the list with y
        for s in xrange(len(sc)-1):     #creating the segments
            d= Segment_2(sc[s],sc[s+1])
            if not d.is_degenerate():
                out.append(d)
    return out

def randpoints_in_faces(dcel):
    frand=[]
    for f in dcel.faces:
        if not f.external:
            if len(f.lvertices) > 3: #if > 4 points intersect 2 diagonials
                c1=Circle_2(f.lvertices[0],f.lvertices[1]).center()
                c2=Circle_2(f.lvertices[2],f.lvertices[3]).center()
                c3=Circle_2(f.lvertices[0],f.lvertices[3]).center()
                c4=Circle_2(f.lvertices[2],f.lvertices[1]).center()                
                sd1 = Segment_2(c1,c2)
                sd2 = Segment_2(c3,c4)
                po = intersection(sd1,sd2)
                frand.append(po)
            elif len(f.lvertices) == 3:   #if 3 find centroid
                c1=Circle_2(f.lvertices[0],f.lvertices[1])
                c2=Circle_2(f.lvertices[1],f.lvertices[2])
                po = intersection(Segment_2(f.lvertices[2],c1.center()),Segment_2(f.lvertices[0],c2.center()))
                frand.append(po)
    return frand
    
def empty_lists(list):
    for l in list:
        if l != []:
            return False
    return True
    
    
def Crit_Cons(p):
    points =[]
    ponbound = []
    critical = []
    perime=[]
    visual=[]

    for e in p.edges:
        visual.append(VSegment_2(e))
        perime.append(e)
    sleep(10)
    for t in p.vertices:
        points.append(t)

    for c in critical_constraints(p):
        if c[1] not in ponbound:
            if p.has_on_boundary(c[1]):
                ponbound.append(c[1])
                if c[1] not in points:
                    points.append(c[1])
            critical.append(c)
            visual.append(VSegment_2(c,color = (1,0,0)))   
    return visual, critical,points,ponbound,perime

def watch(p,visual,frand):
    watches=[]
    li=[]
    ret =[]
    visual1=[]
    for t in p.vertices:        #for every vertex
        what = []
        li.append(t)
        for poi in range(len(frand)):    # for every face (through the random point)
            inte = False
            for ed in p.edges:      
                rt = intersection(ed,Segment_2(t,frand[poi]))   #if there is not an interesect with the perimeter
                if is_Point_2(rt) and clean_inter(ed,Segment_2(t,frand[poi]),rt):
                    inte = True
                    break
            if not inte:
                what.append(poi)    #append in the watch list
        watches.append(what)

    times = floor(len(p.vertices)/3)
    tt=0
    strin = "".join(["%s" % el for el in range(len(p))])
    set1 = set()
    rt = False
    for t in range(1,times):
       s = combinations(strin,t)
       for ne in s:
         for ps in ne:
           set1.update(watches[int(ps)])
         if len(set1) == len(frand):
          ret = ne
          rt = True
          break
         set1.clear()
       if rt:
        break
    
    list_in=[]
    if len(ret) !=0:
    	for we in ret:
     	 visual1.append(VPoint_2(li[int(we)],color=(1,1,0)))
     	 list_in.append(li[int(we)])

    print list_in
    sleep(5)

    removing =[]
    while not empty_lists(watches):
        max = 0
        nmax = watches[0]
        for x in xrange(1,len(watches)):
            if len(nmax) < len(watches[x]):
                max = x
                nmax = watches[x]
        if li[max] not in list_in:
           visual.append(VPoint_2(li[max],color=(0,1,0)))
        else:
           visual.append(VPoint_2(li[max],color=(1,0,1)))
        li.pop(max)
        print max
        removing = watches[max]
        watches.pop(max)
        for we in watches:
            for w in removing:
                try:
                    we.remove(w)
                except:
                    continue
        #print watches
        tt +=1
        
    print "Maximum number of guards: " ,times ,"\nGuards algorithm places: ", tt, "\nBest fit places: ", len(visual1)
    return visual1

def Guard_museum(p):
    expo=[]
    visual , critical, points, ponbound, perime = Crit_Cons(p)

    print "Give the points for the exhibits"
    click = mouseClick()
    while click.button <> 'right':
        if p.has_on_bounded_side(Point_2(click.pos.x, click.pos.y)):
            expo.append(VPoint_2(click.pos.x, click.pos.y,color=(0,1,1)))
        else:
            print "Please give a point inside the 'museum'"
        click = mouseClick()
    
    ###create the segments
    nncritical = seg_create(critical,perime,points)   #inside segments
    out=slice_perimeter(p,ponbound)              #perimeter segments


    ncritical = nncritical
    ncritical += out

    dcel = Dcel(points,ncritical)       #creatng dcel 
    frand=randpoints_in_faces(dcel)     #create the rand points in every face

    df = watch(p,visual,frand)
    return visual,df,expo
#
# Important stuff ends here
#

def rand_simple_polygon(vertices):
    """
    That's an unreliable hack to generate a random
    simple polygon. 
    Beware, sometimes it is stuck in an infinite loop.
    """
    poly = Polygon_2()
    while vertices > 0:
        x = randint(-5, 5) * 10
        y = randint(-5, 5) * 10
        poly.push_back(Point_2(x,y))
        if poly.is_simple():
            point_found = True
            vertices -= 1
        else:
            del poly[-1]
    return poly
'''
def coloring(triangs):
    blue=[]
    red=[]
    green=[]
    while triangs != []:
        for P in triangs:
            if blue == red == green == []:
                blue.append(P[0])
                green.append(P[1])
                red.append(P[2])
                triangs.remove(P)
                continue
            if P[0] in blue:
                if P[1] in red:
                    if P[2] not in green:
                        green.append(P[2])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[1] in green:
                    if P[2] not in red:
                        red.append(P[2])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[2] in red:
                    if P[1] not in green:
                        green.append(P[1])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[2] in green:
                    if P[1] not in red:
                        red.append(P[1])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
            elif P[0] in red:
                if P[1] in blue:
                    if P[2] not in green:
                        green.append(P[2])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[1] in green:
                    if P[2] not in blue:
                        blue.append(P[2])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[2] in blue:
                    if P[1] not in green:
                        green.append(P[1])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[2] in green:
                    if P[1] not in blue:
                        blue.append(P[1])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
            if P[0] in green:
                if P[1] in red:
                    if P[2] not in blue:
                        blue.append(P[2])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[1] in blue:
                    if P[2] not in red:
                        red.append(P[2])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[2] in red:
                    if P[1] not in blue:
                        blue.append(P[1])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[2] in blue:
                    if P[1] not in red:
                        red.append(P[1])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
            elif P[1] in blue:
                if P[0] in red:
                    if P[2] not in green:
                        green.append(P[2])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[0] in green:
                    if P[2] not in red:
                        red.append(P[2])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[2] in red:
                    if P[0] not in green:
                        green.append(P[0])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[2] in green:
                    if P[0] not in red:
                        red.append(P[0])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
            elif P[1] in red:
                if P[0] in blue:
                    if P[2] not in green:
                        green.append(P[2])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[0] in green:
                    if P[2] not in blue:
                        blue.append(P[2])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[2] in blue:
                    if P[0] not in green:
                        green.append(P[0])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[2] in green:
                    if P[0] not in blue:
                        blue.append(P[0])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
            if P[1] in green:
                if P[0] in red:
                    if P[2] not in blue:
                        blue.append(P[2])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[0] in blue:
                    if P[2] not in red:
                        red.append(P[2])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[2] in red:
                    if P[0] not in blue:
                        blue.append(P[0])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[2] in blue:
                    if P[0] not in red:
                        red.append(P[0])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
            if P[2] in blue:
                if P[1] in red:
                    if P[0] not in green:
                        green.append(P[0])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[1] in green:
                    if P[0] not in red:
                        red.append(P[0])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[0] in red:
                    if P[1] not in green:
                        green.append(P[1])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[0] in green:
                    if P[1] not in red:
                        red.append(P[1])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
            elif P[2] in red:
                if P[1] in blue:
                    if P[0] not in green:
                        green.append(P[0])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[1] in green:
                    if P[0] not in blue:
                        blue.append(P[0])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[0] in blue:
                    if P[1] not in green:
                        green.append(P[1])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[0] in green:
                    if P[1] not in blue:
                        blue.append(P[1])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
            if P[2] in green:
                if P[1] in red:
                    if P[0] not in blue:
                        blue.append(P[0])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[1] in blue:
                    if P[0] not in red:
                        red.append(P[0])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[0] in red:
                    if P[1] not in blue:
                        blue.append(P[1])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
                elif P[0] in blue:
                    if P[1] not in red:
                        red.append(P[1])
                        triangs.remove(P)
                        continue
                    else:
                        triangs.remove(P)
                        continue
    return blue,red,green
'''

########################################################################

#po,ps = getPolygon()

po = [pu(0,0),pu(30,0),pu(30,15),pu(15,15),pu(15,30),pu(30,30),pu(30,60),pu(0,60),pu(0,50),pu(15,50),pu(15,40),pu(0,40)]
p = Polygon_2(po)
print p 
P = po[:]

print "Polygon:", p
print "Acute Vertices:", [p[i] for i in acute_vertices(p)]

visual,df,expo = Guard_museum(p)
vis=[]
    
print "End of critical"
'''
dt =  Constrained_triangulation_2()
for i in po:
    dt.insert(i)
    
for seg in ps:
    dt.insert_constraint(seg.start(),seg.end())
Pol=[]

for f in dt.faces:          #Finding inside triangulation
    if not dt.is_infinite(f):
        c1= Circle_2(f.vertex(0).point(),f.vertex(1).point())
        c2= Circle_2(f.vertex(0).point(),f.vertex(2).point())
        c3= Circle_2(f.vertex(2).point(),f.vertex(1).point())
        ce1=c1.center()
        ce2=c2.center()
        ce3=c3.center()
        if (p.has_on_boundary(ce1) or p.has_on_bounded_side(ce1)) and (p.has_on_boundary(ce2) or p.has_on_bounded_side(ce2)) and (p.has_on_boundary(ce3) or p.has_on_bounded_side(ce3)):
            d = [f.vertex(0),f.vertex(1),f.vertex(2)]
            Pol.append(d)
blue,red,green = coloring(Pol)

print "blue ",len(blue),",red ",len(red),",green ",len(green)
less=[len(blue),len(red),len(green)]
l = min(less)
print "The Chavatal needs ",l," guards"
'''
print "END"
