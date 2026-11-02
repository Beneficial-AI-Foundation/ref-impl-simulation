-- Fixture for check-short-names.py: the name of `A.B.g` is on the line after `def`.
-- In its body, `t` binds to `foo.A.t`, not to the crate-level `foo.t`.
namespace foo
def A.t : Nat := 1
def t : Nat := 2
def
  A.B.g : Nat := t
end foo
