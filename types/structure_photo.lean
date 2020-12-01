structure Photo : Type :=
mk :: (caption : string) (filename : string) (rating : ℕ)

open Photo

def change_rating : Photo → ℕ → Photo :=
λ p n, 
    Photo.mk p.caption p.filename n


def change_rating' (p : Photo) (n : ℕ) : Photo :=
    Photo.mk p.caption p.filename n


def change_rating'' : Photo → ℕ → Photo
| p n := Photo.mk p.caption p.filename n


def change_caption : Photo → string → Photo :=
    λ p s, Photo.mk s p.filename p.rating


def change_filename : Photo → string → Photo :=
    λ p s, Photo.mk p.caption s p.rating



def p1 := Photo.mk "a caption" "a_file/foo.jpg" 5
def p2 := change_rating p1 3

#eval p1.caption
#eval p1.filename
#eval p1.rating

#eval p2.caption
#eval p2.filename
#eval p2.rating