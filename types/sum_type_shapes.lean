/-
We define a simple example of a shape library
of the kind that might be used in a computer
graphics or gaming application.
-/



/-
Each pixel on the screen is represented by a 
set of 2-D coordinates, which are rerally just
ordered pairs of natural numbers. (0,0) is the
pixel in the upper left of the screen. The "x"
axis of the coordinate system appears in the
first element of a pair, with x increasing as
one moves to the right. The position of a pixel
on the "y" axis is represented by the second
element of a pair, with y increasing as one
moves down the screen. (Yep, that is generally
how one addresses pixels on a screen.) 
-/
structure coords : Type :=
mk :: (x : ℕ) (y : ℕ)
/-
Note that by using "structure" here, we get
coords.x and coords.y as projection funtions
(accessors/getters) for free.
-/


/-
Now we specific "shape" as a sum type, that is 
as a variant type, with point, segment, triangle,
and rectangle as the variants. Each variant has
a constructor. Each constsructor takes the right
number of coordinates (pairs) to specific a shape
of that kind. A point is constructed with one pair
of coords, a segment with two pairs, triangle with
three, etc.
-/
inductive shape : Type
| point : coords → shape
| segment: coords → coords → shape
| triangle : coords → coords → coords → shape
| rectangle : coords → coords → coords → coords → shape

/-
It would be accurate to describe this type as
a sum of product types. There is a different kind
of tuple/record/structure for each variant. A point
is built with one pair, a segment with two, etc.
-/

/-
Now when we want to define a function that
operates on values of this type (that takes
a shape as an argument), we have to define
the result of the function for each possible
value of the type, which means describing how
the function computes a result for each form,
or variant, of shape.

To distinguish different forms we use --- no
real surprises here -- pattern matching. We
give one example: a function that when given
any of the four shapes, returns a string that
describes that shape: "point" for points, etc.
This result of this function doesn't depend on
the specific coordinates of the "vertices" in 
each shape, so we use underscores to match but
not to name the coord arguments to each of the
constructors.
-/

def toString (s : shape) :=
match s with
| (shape.point _) := "point"
| (shape.segment _ _) := "segment"
| (shape.triangle _ _ _) := "triangle"
| (shape.rectangle _ _ _ _) := "rectangle"
end

def toString' : shape → string :=
λ (s : shape),
match s with
| (shape.point _) := "point"
| (shape.segment _ _) := "segment"
| (shape.triangle _ _ _) := "triangle"
| (shape.rectangle _ _ _ _) := "rectangle"
end

def toString'' : shape → string
| (shape.point _) := "point"
| (shape.segment _ _) := "segment"
| (shape.triangle _ _ _) := "triangle"
| (shape.rectangle _ _ _ _) := "rectangle"




def toString' : shape → string :=
λ s,
match s with
| (shape.point _) := "point"
| (shape.segment _ _) := "segment"
| (shape.triangle _ _ _) := "triangle"
| (shape.rectangle _ _ _ _) := "rectangle"
end

def toString'' : shape → string
| (shape.point _) := "point"
| (shape.segment _ _) := "segment"
| (shape.triangle _ _ _) := "triangle"
| (shape.rectangle _ _ _ _) := "rectangle"


#eval toString (shape.segment (coords.mk 3 4) (coords.mk 2 9))
/-
In summary, what you have here is a new kind of
example of an inductive type: one with multiple
constructors, each taking one or more arguments:
a "sum of products" type. And you've seen how we
use pattern matching to decide what variant form
of value a function is being applied to, in order
to produce an appropriate return value.
-/

/-
Testing. We define three coords objects, called 
c1, c2, and c3, and then use them to build three
shape objects p1, a point; s1, a segment; and t1,
a triangle.
-/
def c1 := coords.mk 2 3
def c2 := coords.mk 5 11
def c3 := coords.mk 4 8

def p1 := shape.point c1
def s1 := shape.segment c1 c2
def t1 := shape.triangle c1 c2 c3

#reduce s1

#eval toString p1
#eval toString s1