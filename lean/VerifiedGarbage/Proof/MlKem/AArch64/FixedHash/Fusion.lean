module
public import VerifiedGarbage.Proof.Framework.CallFill
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Mem
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash.Fusion
open VG
variable {M : ISA}

def Same (a b : Prog M) : Prop := ∀s tr t,Exec M a s tr t ↔ Exec M b s tr t

theorem Same.refl (a : Prog M) : Same a a := fun _ _ _=>Iff.rfl
theorem Same.symm {a b : Prog M} (h : Same a b) : Same b a := fun s tr t=>(h s tr t).symm
theorem Same.trans {a b c : Prog M} (h : Same a b) (g : Same b c) : Same a c :=
 fun s tr t=>(h s tr t).trans (g s tr t)

theorem Same.wp {a b : Prog M} (h : Same a b) {s : M.State} {Q : M.State→Prop} :
 WP M a s Q ↔ WP M b s Q := by
 constructor <;> rintro ⟨tr,t,he,hq⟩
 · exact ⟨tr,t,(h s tr t).mp he,hq⟩
 · exact ⟨tr,t,(h s tr t).mpr he,hq⟩

theorem Same.relCT {a b : Prog M} (h : Same a b) {P Q : M.State→M.State→Prop}
 (hc : RelCT M P a Q) : RelCT M P b Q := by
 intro s u tr ur t v hp he hf
 exact hc s u tr ur t v hp ((h s tr t).mpr he) ((h u ur v).mpr hf)

theorem seq_congr {a b c d : Prog M} (h : Same a b) (g : Same c d) :
 Same (.seq a c) (.seq b d) := by
 intro s tr t
 constructor
 · intro he; cases he with
   | seq e f => exact .seq ((h ..).mp e) ((g ..).mp f)
 · intro he; cases he with
   | seq e f => exact .seq ((h ..).mpr e) ((g ..).mpr f)

theorem block_append (xs ys : List M.Instr) : Same (.seq (.block xs) (.block ys)) (.block (xs++ys)) := by
 intro s tr t
 constructor
 · intro he; cases he with
   | seq e f =>
     cases e with
     | block e =>
       cases f with
       | block f =>
         exact .block (by rw [execBlock_append,e]; simp only [Option.bind_some,f,Option.map_some])
 · intro he
   rw [Exec.block_iff,execBlock_append] at he
   obtain ⟨⟨u,ta⟩,ha,hb⟩ := Option.bind_eq_some_iff.mp he
   obtain ⟨⟨v,tb⟩,hc,hd⟩ := Option.map_eq_some_iff.mp hb
   simp only [Prod.mk.injEq] at hd
   obtain ⟨rfl,rfl⟩:=hd
   exact .seq (.block ha) (.block hc)

theorem nil_left (a : Prog M) : Same (.seq (.block []) a) a := by
 intro s tr t
 constructor
 · intro he; cases he with
   | seq e f =>
     rw [Exec.block_iff] at e
     simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at e
     obtain ⟨rfl,rfl⟩:=e
     exact f
 · intro he
   simpa only [List.nil_append] using (Exec.seq (Exec.block (by rfl : execBlock M [] s=some (s,[]))) he)

theorem nil_right (a : Prog M) : Same (.seq a (.block [])) a := by
 intro s tr t
 constructor
 · intro he; cases he with
   | seq e f =>
     rw [Exec.block_iff] at f
     simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at f
     obtain ⟨rfl,rfl⟩:=f
     simpa only [List.append_nil] using e
 · intro he
   simpa only [List.append_nil] using (Exec.seq he (Exec.block (by rfl : execBlock M [] t=some (t,[]))))

theorem assoc (a b c : Prog M) : Same (.seq (.seq a b) c) (.seq a (.seq b c)) := by
 intro s tr t
 constructor
 · intro he; cases he with
   | seq e f => cases e with
     | seq g h => simpa only [List.append_assoc] using (Exec.seq g (Exec.seq h f))
 · intro he; cases he with
   | seq e f => cases f with
     | seq g h => simpa only [List.append_assoc] using (Exec.seq (Exec.seq e g) h)

/-- Concatenate code, flattening sequences and coalescing adjacent blocks. -/
def append : Prog M → Prog M → Prog M
 | .seq a b,c => append a (append b c)
 | .block [],c => c
 | .block xs,.block ys => .block (xs++ys)
 | .block xs,.seq (.block ys) c => .seq (.block (xs++ys)) c
 | a,.block [] => a
 | a,b => .seq a b

theorem append_same (a b : Prog M) : Same (.seq a b) (append a b) := by
 induction a generalizing b with
 | seq a c ia ic =>
   exact (assoc a c b).trans ((seq_congr (Same.refl a) (ic b)).trans (ia (append c b)))
 | block xs =>
   cases xs with
   | nil => exact nil_left b
   | cons x xs =>
     cases b with
     | block ys => exact block_append _ _
     | seq b c =>
       cases b with
       | block ys =>
         exact (assoc (.block (x::xs)) (.block ys) c).symm.trans
           (seq_congr (block_append _ _) (Same.refl c))
       | _ => exact Same.refl _
     | _ => exact Same.refl _
 | _ =>
   cases b with
   | block ys => cases ys with
     | nil => exact nil_right _
     | cons y ys => exact Same.refl _
   | _ => exact Same.refl _

/-- Normalize sequence grouping and block boundaries without changing calls. -/
def normalize : Prog M → Prog M
 | .seq a b => append (normalize a) (normalize b)
 | a => a

theorem normalize_same (a : Prog M) : Same a (normalize a) := by
 induction a with
 | seq a b ha hb => exact (seq_congr ha hb).trans (append_same _ _)
 | _ => exact Same.refl _

/-- Equality of normal forms certifies exact state and leakage equivalence. -/
theorem of_normalize_eq {a b : Prog M} (h : normalize a=normalize b) : Same a b :=
 (normalize_same a).trans (h ▸ (normalize_same b).symm)

/-! ## Code with its holes filled

`append` and `normalize` look at blocks and sequences only, which filling
holes (`Code.fillHoles`) keeps, so they commute with it: two programs whose
code with holes has the same normal form are the same with the holes filled
by any callee (`Same.of_fillHoles`). -/

/-- Filling holes keeps blocks, and makes no block of anything else. -/
theorem fillHoles_block {n : String} {b : Prog M} {a : Prog M} {xs : List M.Instr}
    (h : Code.fillHoles n b a = .block xs) : a = .block xs := by
  cases a with
  | block is => exact h
  | call m body =>
    cases body with
    | block is => cases is <;> cases h
    | _ => cases h
  | _ => cases h

/-- Filling holes keeps sequences, and makes no sequence of anything else. -/
theorem fillHoles_seq {n : String} {b : Prog M} {a x y : Prog M}
    (h : Code.fillHoles n b a = .seq x y) : ∃ a₁ a₂, a = .seq a₁ a₂ := by
  cases a with
  | seq a₁ a₂ => exact ⟨a₁, a₂, rfl⟩
  | call m body =>
    cases body with
    | block is => cases is <;> cases h
    | _ => cases h
  | _ => cases h

theorem fillHoles_append (n : String) (b : Prog M) (a c : Prog M) :
    Code.fillHoles n b (append a c) = append (Code.fillHoles n b a) (Code.fillHoles n b c) := by
  induction a generalizing c with
  | seq a₁ a₂ ih₁ ih₂ => simp only [append, Code.fillHoles, ih₁, ih₂]
  | block xs =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases c with
      | block ys => rfl
      | seq c₁ c₂ =>
        cases c₁ with
        | block ys => rfl
        | call m body =>
          cases body with
          | block is => cases is <;> rfl
          | _ => rfl
        | _ => rfl
      | call m body =>
        cases body with
        | block is => cases is <;> rfl
        | _ => rfl
      | _ => rfl
  | call m body =>
    cases body with
    | block is =>
      cases is with
      | nil =>
        cases c with
        | block ys => cases ys <;> rfl
        | call m' body' =>
          cases body' with
          | block is' => cases is' <;> rfl
          | _ => rfl
        | _ => rfl
      | cons i is =>
        cases c with
        | block ys => cases ys <;> rfl
        | call m' body' =>
          cases body' with
          | block is' => cases is' <;> rfl
          | _ => rfl
        | _ => rfl
    | _ =>
      cases c with
      | block ys => cases ys <;> rfl
      | call m' body' =>
        cases body' with
        | block is' => cases is' <;> rfl
        | _ => rfl
      | _ => rfl
  | _ =>
    cases c with
    | block ys => cases ys <;> rfl
    | call m' body' =>
      cases body' with
      | block is' => cases is' <;> rfl
      | _ => rfl
    | _ => rfl

theorem normalize_fillHoles (n : String) (b : Prog M) (a : Prog M) :
    normalize (Code.fillHoles n b a) = Code.fillHoles n b (normalize a) := by
  induction a with
  | seq x y ihx ihy => simp only [Code.fillHoles, normalize, ihx, ihy, fillHoles_append]
  | call m body =>
    cases body with
    | block is => cases is <;> rfl
    | _ => rfl
  | _ => rfl

/-- `a` and `b` are the code with holes `a₀` and `b₀` with the holes filled:
if `a₀` and `b₀` have the same normal form, `a` and `b` are the same. -/
theorem Same.of_fillHoles {a b a₀ b₀ : Prog M} {n : String} {body : Prog M}
    (ha : a = Code.fillHoles n body a₀) (hb : b = Code.fillHoles n body b₀)
    (h : normalize a₀ = normalize b₀) : Same a b :=
  of_normalize_eq (by rw [ha, hb, normalize_fillHoles, normalize_fillHoles, h])

end VG.Proof.MlKem.AArch64.FixedHash.Fusion
