"""
CGAL DCEL implemanation
By Georgios Koloventzos
DCEL First Implemantation
Download-URL: https://netfiles.uiuc.edu/ayg/www/stuff/dcel-0.1.0.tar.gz
By Angel Yanguas-Gil
"""
from CGAL import *
from math import *
from cgalvisual import *

def collinear(i, j, k):
	return orientation(i, j, k) == CGAL.Kernel.Sign.EQUAL
    
class Vertex:
    """Minimal implementation of a vertex of a 2D dcel"""
    
    def __init__(self, point_2):
        self.x = point_2.x()
        self.y = point_2.y()
        self.hedgelist = []

    def sortincident(self):
        self.hedgelist.sort(hsort, reverse=True)
        
########################################################################

class Hedge:
    """Minimal implementation of a half-edge of a 2D dcel"""

    def __init__(self,segment_2):
        #The origin is defined as the vertex it points to
        self.v2 = segment_2.end()
        self.v1 = segment_2.start()
        self.origin = segment_2.target()
        self.twin = None
        self.face = None
        self.nexthedge = None
        self.angle = hangle(self.v2.x()-self.v1.x(), self.v2.y()-self.v1.y())
        self.prevhedge = None
        self.length = sqrt(segment_2.squared_length())
        

    def start(self):
        return self.v1
    
    def end(self):
        return self.v2
########################################################################

class Face:
    """Implements a face of a 2D dcel"""

    def __init__(self):
        self.wedge = None
        self.lvertices = []
        self.ledges = []
        self.data = None
        self.external = None

    def area(self):
        h = self.wedge
        a = 0
        while(not h.nexthedge is self.wedge):
            p1 = h.origin
            p2 = h.nexthedge.origin
            a += p1.x()*p2.y() - p2.x()*p1.y()
            h = h.nexthedge

        p1 = h.origin
        p2 = self.wedge.origin
        a = (a + p1.x()*p2.y() - p2.x()*p1.y())/2
        return a

    def perimeter(self):
        p=0
        for h in ledges:
            p += h.length
        return p

    def isinside(self, p):
        """Determines whether a point is inside a face"""

        for h in ledges:
            if lefton(h,p):
                continue
            else:
                return False
        return True

########################################################################

class Dcel():
    """
    Implements a doubly-connected edge list
    """

    def __init__(self, vl=[], el=[]):
        self.vertices = []
        self.hedges = []
        self.faces = []
        if vl == []:
            return False
#Step 1: vertex list creation
        for v in vl:
            self.vertices.append(Vertex(v))

#Step 2: hedge list creation. Assignment of twins and
#vertices
        for e in el:
            h1 = Hedge(e)
            h2 = Hedge(e.opposite())
            h1.twin = h2
            h2.twin = h1
            i = vl.index(e[1])
            j = vl.index(e[0])
            self.vertices[i].hedgelist.append(h1)
            self.vertices[j].hedgelist.append(h2)
            self.hedges.append(h2)
            self.hedges.append(h1)

        #Step 3: Identification of next and prev hedges
        for v in self.vertices:
            v.sortincident()
            l = len(v.hedgelist)
            if l < 2:
                g = VPoint_2(v.x,v.y)
                raise DcelError(
                    "Badly formed dcel: less than two hedges in vertex")
            else:
                for i in range(l-1):
                    v.hedgelist[i].nexthedge = v.hedgelist[i+1].twin
                    v.hedgelist[i+1].prevhedge = v.hedgelist[i]
                v.hedgelist[l-1].nexthedge = v.hedgelist[0].twin
                v.hedgelist[0].prevhedge = v.hedgelist[l-1]            

        #Step 4: Face assignment
        provlist = self.hedges[:]
        nf = 0
        nh = len(self.hedges)

        while nh > 0:
            h = provlist.pop()
            nh -= 1
            #We check if the hedge already points to a face
            if h.face == None:
                f = Face()
                nf += 1
                #We link the hedge to the new face
                f.wedge = h
                f.wedge.face = f
                f.ledges.append(h)
                f.lvertices.append(h.end())
                #And we traverse the boundary of the new face
                while (not h.nexthedge is f.wedge):
                    h = h.nexthedge
                    f.ledges.append(h)
                    f.lvertices.append(h.end())
                    h.face = f
                self.faces.append(f)
        #And finally we have to determine the external face
        for f in self.faces:
            f.external = f.area() < 0


    def findpoints(self, pl, onetoone=False):
        """Given a list of points pl, returns a list of 
        with the corresponding face each point belongs to and
        None if it is outside the map.
        
        """
        
        ans = []
        if onetoone:
            fl = self.faces[:]
            for p in pl:
                found = False
                for f in fl:
                    if f.external:
                        continue
                    if f.isinside(p):
                        fl.remove(f)
                        found = True
                        ans.append(f)
                        break
                if not found:
                    ans.append(None)

        else:
            for p in pl:
                found = False
                for f in self.faces:
                    if f.external:
                        continue
                    if f.isinside(p):
                        found = True
                        ans.append(f)
                        break
                if not found:
                    ans.append(None)

        return ans

    def areas(self):
        return [f.area() for f in self.faces if not f.external]

    def perimeters(self):
        return [f.perimeter() for f in self.faces if not f.external]

    def nfaces(self):
        return len(self.faces)

    def nvertices(self):
        return len(self.vertices)

    def nedges(self):
        return len(self.hedges)/2
########################################################################

def hsort(h1, h2):
    """Sorts two half edges counterclockwise"""

    if h1.angle < h2.angle:
        return -1
    elif h1.angle > h2.angle:
        return 1
    else:
        return 0


def checkhedges(hl):
    """Consistency check of a hedge list: nexthedge, prevhedge"""

    for h in hl:
        if h.nexthedge not in hl or h.prevhedge not in hl:
            raise DcelError("Problems with an orphan hedge...")


def area2(hedge, point):
    """Determines the area of the triangle formed by a hedge and
    an external point"""
    
    pa = hedge.twin.origin
    pb=hedge.origin
    pc=point
    t.Triangle(pa,pb,pc)
    return t.area()


def lefton(hedge, point):
    """Determines if a point is to the left of a hedge"""

    return orientation(hedge.start(),hedge.end(),point) == CGAL.Kernel.Sign.LARGER


def hangle(dx,dy):
    """Determines the angle with respect to the x axis of a segment
    of coordinates dx and dy
    """
    l = sqrt(dx*dx + dy*dy)
    if dy > 0:
        return acos(dx/l)
    else:
        return 2*pi - acos(dx/l)
