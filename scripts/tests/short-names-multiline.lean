-- Fixture for check-short-names.py: declarations whose name is on a later line than `def`.
-- In both bodies, `t` binds to `foo.A.t`, not to the crate-level `foo.t`.
namespace foo
def A.t : Nat := 1
def t : Nat := 2
def
  A.B.g : Nat := t
def

  -- a comment between the keyword and the name
  A.C.h : Nat := t
end foo
