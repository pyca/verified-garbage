module

public import VerifiedGarbage.Impl.CmacTripleDes.X86.Ssse3
public import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Core
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Frame
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.CmacTripleDes.X86.Ssse3Lit
import VerifiedGarbage.Proof.CmacTripleDes.Words
import VerifiedGarbage.Proof.CmacTripleDes.Bytes
import VerifiedGarbage.Proof.CmacTripleDes.Cmac
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.CallBody
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.CmacTripleDes.X86.Update
import VerifiedGarbage.Proof.CmacTripleDes.X86.Finalize
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Modes.X86.Ops
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.CmacTripleDes.X86.Ssse3
meta import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Core
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Frame
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.Ssse3Lit
meta import VerifiedGarbage.Proof.CmacTripleDes.Words
meta import VerifiedGarbage.Proof.CmacTripleDes.Bytes
meta import VerifiedGarbage.Proof.CmacTripleDes.Cmac
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.TripleDes.Schedule
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Proof.Framework.X86.SymFrame
meta import VerifiedGarbage.Proof.Framework.X86.CallBody
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.Update
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.Finalize
meta import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Modes.X86.Ops
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# Streaming TDEA-CMAC with Triple DES's S-boxes by `pshufb` on x86 (32-bit) meets its contracts
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.X86.Ssse3

open VG VG.X86 VG.X86.Wp
open VG.Impl.CmacTripleDes.X86.Ssse3
open VG.Impl.Modes.X86 (sb at_)
open VG.Impl.TripleDes.X86.Ssse3 (key crypt tableName blkOff)
open VG.Proof.TripleDes.X86.Ssse3 (sa Keys kq ord keyAt_wp crypt_blk rdw_same rdw_ne ord_lo ord_mid ord_hi
  sched_read keys_contains keyOff_eq count_loop add4 addr_add)
open VG.Spec.TripleDes (Schedule)
open VG.Spec.Aes (bytesAt)

/-- The offset of the rounds' keys in the block function's buffer. -/
local notation "kO" => VG.Impl.TripleDes.X86.Ssse3.keyOff

/-! ## One instruction at a time -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov d, [b + o]`, at the address `a`. -/
theorem ld {d b : Reg} {o : Nat} {B : BitVec 32} {a : Addr} (hb : s.gpr b = B) (ha : addr B o = a)
    (hin : InRegions (s.rd ++ s.wr) a 4) (k : ∀ s', Upd s s' d (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (at_ b o)) :: is)) s Q := by
  subst ha; exact wp_ldm hb hin k

/-- `mov [b + o], r`, at the address `a`. -/
theorem st {b r : Reg} {o : Nat} {B : BitVec 32} {a : Addr} (hb : s.gpr b = B) (ha : addr B o = a)
    (hout : InRegions s.wr a 4) (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr r)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store (at_ b o) r :: is)) s Q := by
  subst ha; exact wp_stm hb hout k

/-- `xor d, [b + o]`, at the address `a`. -/
theorem xm {d b : Reg} {o : Nat} {B : BitVec 32} {a : Addr} (hb : s.gpr b = B) (ha : addr B o = a)
    (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem (at_ b o)) :: is)) s Q := by
  subst ha; exact wp_xorm hb hin k

/-- `movzx d, byte [b + o]`, at the address `a`. -/
theorem lb {d b : Reg} {o : Nat} {B : BitVec 32} {a : Addr} (hb : s.gpr b = B) (ha : addr B o = a)
    (hin : InRegions (s.rd ++ s.wr) a 1) (k : ∀ s', Upd s s' d ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d (at_ b o) :: is)) s Q := by
  subst ha; exact VG.Proof.Modes.X86.wp_movzx hb hin k

/-- `mov byte [b + o], r8`, at the address `a`. -/
theorem sb8 {b : Reg} {r : Reg8} {o : Nat} {B : BitVec 32} {a : Addr} (hb : s.gpr b = B) (ha : addr B o = a)
    (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 (at_ b o) r :: is)) s Q := by
  subst ha; exact VG.Proof.Modes.X86.wp_st8 hb hout k

end

/-- An address at an offset, which does not wrap. -/
theorem a0 {P : BitVec 32} {a c : Nat} (hc : a = c) (h : P.toNat + c < 2 ^ 32) :
    addr P a = P.setWidth 64 + BitVec.ofNat 64 c := by
  subst hc; exact addr_eq h

theorem a4 {P : BitVec 32} {a c : Nat} (hc : a = c + 4) (h : P.toNat + (c + 4) < 2 ^ 32) :
    addr P a = P.setWidth 64 + BitVec.ofNat 64 c + 4 := by
  subst hc; exact (addr_eq h).trans (add4 _ _).symm

/-- The address in a register that is a base. -/
theorem az (P : BitVec 32) : addr P 0 = P.setWidth 64 := by simp [addr]

/-! ## The rounds' keys, at fixed offsets -/

/-- A round's keys of the three passes. -/
def keys3 (t : Nat) : List Instr :=
  key .eax (8 * t) (kO + 8 * t) ++ key .eax (248 - 8 * t) (kO + 128 + 8 * t) ++
    key .eax (256 + 8 * t) (kO + 256 + 8 * t)

theorem keys_eq : keys = (List.range' 0 16).flatMap keys3 := by
  rw [keys, List.range_eq_range']; rfl

/-- The keys' conversion, before the round `t` of each of the three passes. -/
structure KI (s₁ : State) (B : BitVec 32) (k : Schedule) (t : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .ebx → r ≠ .ebp → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  syms : s.syms = s₁.syms
  frame : Frame [⟨sa B kO, 384⟩] s₁.mem s.mem
  done : ∀ i < 48, i % 16 < t → s.mem.readW (sa B (kO + 8 * i)) 64 = kq (k.getD (ord i) 0)

/-- A round's keys of the three passes. -/
theorem keys3_wp {s₁ s : State} {B P : BitVec 32} {k : Schedule} {t N : Nat} {is : List Instr} {Q : State → Prop}
    (hP : s₁.gpr .eax = P) (hB : s₁.gpr .esi = B)
    (hrs : (⟨P.setWidth 64, 384⟩ : Region) ∈ s₁.rd ++ s₁.wr) (hN : 432 ≤ N)
    (hw : (⟨B.setWidth 64, N⟩ : Region) ∈ s₁.wr)
    (hdis : Region.Disjoint ⟨P.setWidth 64, 384⟩ ⟨B.setWidth 64, N⟩)
    (fP : P.toNat + 384 ≤ 2 ^ 32) (fB : B.toNat + N ≤ 2 ^ 32)
    (hS : ∀ i < 48, s₁.mem.readW (P.setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = k.getD i 0)
    (ht : t < 16) (h : KI s₁ B k t s) (k' : ∀ s', KI s₁ B k (t + 1) s' → WP isa (.block is) s' Q) :
    WP isa (.block (keys3 t ++ is)) s Q := by
  obtain hrs' : (⟨P.setWidth 64, 384⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd, h.wr]; exact hrs
  obtain hw' : (⟨B.setWidth 64, N⟩ : Region) ∈ s.wr := by rw [h.wr]; exact hw
  have hko := keyOff_eq
  rw [keys3, List.append_assoc, List.append_assoc]
  refine keyAt_wp (i := t) (i' := t) ((h.gpr _ (by decide) (by decide)).trans hP)
    ((h.gpr _ (by decide) (by decide)).trans hB) (by decide) (by decide)
    (a0 rfl (by omega_arith)) (a4 rfl (by omega_arith)) (a0 rfl (by omega_arith)) (a4 rfl (by omega_arith))
    (by omega_arith) (by omega_arith) hrs' hN hw' hdis
    ((sched_read h.frame hN hdis (by omega_arith)).trans (hS _ (by omega_arith))) fun s₂ m₂ g₂ rd₂ wr₂ sy₂ => ?_
  obtain f₂ : Frame [⟨sa B kO, 384⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact h.frame.writeW (List.mem_singleton_self _) _ (keys_contains B (by omega_arith))
  obtain G₂ : ∀ r, r ≠ .ebx → r ≠ .ebp → s₂.gpr r = s₁.gpr r := fun r a b => (g₂ r a b).trans (h.gpr r a b)
  refine keyAt_wp (i := 31 - t) (i' := 16 + t) ((G₂ _ (by decide) (by decide)).trans hP)
    ((G₂ _ (by decide) (by decide)).trans hB) (by decide) (by decide)
    (a0 (by omega_arith) (by omega_arith)) (a4 (by omega_arith) (by omega_arith))
    (a0 (by omega_arith) (by omega_arith)) (a4 (by omega_arith) (by omega_arith))
    (by omega_arith) (by omega_arith) (by rw [rd₂, wr₂]; exact hrs') hN (by rw [wr₂]; exact hw') hdis
    ((sched_read f₂ hN hdis (by omega_arith)).trans (hS _ (by omega_arith))) fun s₃ m₃ g₃ rd₃ wr₃ sy₃ => ?_
  obtain f₃ : Frame [⟨sa B kO, 384⟩] s₁.mem s₃.mem := by
    rw [m₃]; exact f₂.writeW (List.mem_singleton_self _) _ (keys_contains B (by omega_arith))
  obtain G₃ : ∀ r, r ≠ .ebx → r ≠ .ebp → s₃.gpr r = s₁.gpr r := fun r a b => (g₃ r a b).trans (G₂ r a b)
  refine keyAt_wp (i := 32 + t) (i' := 32 + t) ((G₃ _ (by decide) (by decide)).trans hP)
    ((G₃ _ (by decide) (by decide)).trans hB) (by decide) (by decide)
    (a0 (by omega_arith) (by omega_arith)) (a4 (by omega_arith) (by omega_arith))
    (a0 (by omega_arith) (by omega_arith)) (a4 (by omega_arith) (by omega_arith))
    (by omega_arith) (by omega_arith) (by rw [rd₃, wr₃, rd₂, wr₂]; exact hrs') hN (by rw [wr₃, wr₂]; exact hw') hdis
    ((sched_read f₃ hN hdis (by omega_arith)).trans (hS _ (by omega_arith))) fun s₄ m₄ g₄ rd₄ wr₄ sy₄ => ?_
  obtain f₄ : Frame [⟨sa B kO, 384⟩] s₁.mem s₄.mem := by
    rw [m₄]; exact f₃.writeW (List.mem_singleton_self _) _ (keys_contains B (by omega_arith))
  refine k' s₄ ⟨fun r a b => (g₄ r a b).trans (G₃ r a b), ?_, ?_, ?_, f₄, ?_⟩
  · rw [rd₄, rd₃, rd₂]; exact h.rd
  · rw [wr₄, wr₃, wr₂]; exact h.wr
  · rw [sy₄, sy₃, sy₂]; exact h.syms
  · intro i hi hlt
    rw [m₄, m₃, m₂]
    by_cases e2 : i = 32 + t
    · subst e2; rw [rdw_same, ord_hi ht]
    rw [rdw_ne _ _ (Ne.symm e2) (by omega_arith) hi]
    by_cases e1 : i = 16 + t
    · subst e1; rw [rdw_same, ord_mid ht]
    rw [rdw_ne _ _ (Ne.symm e1) (by omega_arith) hi]
    by_cases e0 : i = t
    · subst e0; rw [rdw_same, ord_lo ht]
    rw [rdw_ne _ _ (Ne.symm e0) (by omega_arith) hi]
    exact h.done i hi (by omega_arith)

/-- The keys of the rounds from `t` on. -/
theorem keysFrom_wp {s₁ : State} {B P : BitVec 32} {k : Schedule} {N : Nat} {is : List Instr} {Q : State → Prop}
    (hP : s₁.gpr .eax = P) (hB : s₁.gpr .esi = B)
    (hrs : (⟨P.setWidth 64, 384⟩ : Region) ∈ s₁.rd ++ s₁.wr) (hN : 432 ≤ N)
    (hw : (⟨B.setWidth 64, N⟩ : Region) ∈ s₁.wr)
    (hdis : Region.Disjoint ⟨P.setWidth 64, 384⟩ ⟨B.setWidth 64, N⟩)
    (fP : P.toNat + 384 ≤ 2 ^ 32) (fB : B.toNat + N ≤ 2 ^ 32)
    (hS : ∀ i < 48, s₁.mem.readW (P.setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = k.getD i 0)
    (k' : ∀ s', KI s₁ B k 16 s' → WP isa (.block is) s' Q) :
    ∀ (n t : Nat) (s : State), t + n = 16 → KI s₁ B k t s →
      WP isa (.block ((List.range' t n).flatMap keys3 ++ is)) s Q
  | 0, t, s, e, h => by
    obtain rfl : t = 16 := by omega_arith
    exact k' s h
  | n + 1, t, s, e, h => by
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    exact keys3_wp hP hB hrs hN hw hdis fP fB hS (by omega_arith) h fun s' h' =>
      keysFrom_wp hP hB hrs hN hw hdis fP fB hS k' n (t + 1) s' (by omega_arith) h'

/-! ## Words and bytes -/

open VG.Proof.Cmac (le8 le8_readW le8_xor bytesAt_frame chain_append chain_single)
open VG.Proof.CmacTripleDes (readW64_split)
open VG.Proof.CmacTripleDes.X86 (ciphAt readW_lo_of_hi)

/-- Two words stored at `a` and `a + 4`. -/
theorem pair_le8 (m : Mem) {a x y : Addr} (e0 : x = a) (e4 : y = a + BitVec.ofNat 64 4) (lo hi : BitVec 32) :
    bytesAt ((m.writeW x lo).writeW y hi) a 8 = le8 (hi ++ lo) := by
  subst e0 e4
  rw [← le8_readW, readW64_split, Mem.readW_writeW_self32, readW_lo_of_hi]

/-- The two words at `a` and `a + 4`. -/
theorem le8_pair (m : Mem) {a x y : Addr} (e0 : x = a) (e4 : y = a + BitVec.ofNat 64 4) :
    le8 (m.readW y 32 ++ m.readW x 32) = bytesAt m a 8 := by
  subst e0 e4
  rw [← readW64_split, le8_readW]

/-- `CIPH_K`, as the block function's lemma has it. -/
theorem tdesWith_eq (k : Schedule) : Spec.Cmac.tdesWith k = VG.Proof.TripleDes.dirCipher .encrypt k := rfl

theorem take_succ_blocks (m : Mem) (p : Addr) {n j : Nat} (hj : j < n) :
    (Spec.Cmac.blocksAt m p 8 n).take (j + 1) =
      (Spec.Cmac.blocksAt m p 8 n).take j ++ [bytesAt m (p + BitVec.ofNat 64 (8 * j)) 8] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega_arith)]
  simp [Spec.Cmac.blocksAt]

/-- The rounds' keys stay where memory changes apart from them. -/
theorem keys_frame {m m' : Mem} {B : BitVec 32} {k : Schedule} {rs : List Region} (h : Keys m B k)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨sa B kO, 384⟩ : Region).Disjoint r) : Keys m' B k := fun i hi => by
  rw [← h i hi]
  exact hf.readW (r := ⟨sa B (kO + 8 * i), 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (VG.Offset.sub _ (by omega_arith) (by omega_arith))) (by decide)

/-- A word of the working space, apart from a part of it that changes. -/
theorem slot_keep {m m' : Mem} {S : BitVec 32} {a l o : Nat} (hf : Frame [⟨sa S a, l⟩] m m')
    (h : o + 4 ≤ a ∨ a + l ≤ o) (ha : a + l ≤ 2 ^ 64) (ho : o + 4 ≤ 2 ^ 64) :
    m'.readW (sa S o) 32 = m.readW (sa S o) 32 :=
  hf.readW (r := ⟨sa S o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact VG.Offset.disjoint _ h ho ha) (by decide)

/-- A word of the working space, after its first bytes that change. -/
theorem slot_keep0 {m m' : Mem} {S : BitVec 32} {l o : Nat} (hf : Frame [⟨S.setWidth 64, l⟩] m m')
    (h : l ≤ o) (ho : o + 4 ≤ 2 ^ 64) : m'.readW (sa S o) 32 = m.readW (sa S o) 32 :=
  hf.readW (r := ⟨sa S o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact VG.Offset.disjoint_base _ h ho) (by decide)

/-- A word of the working space, read after a write to another. -/
theorem rds (m : Mem) (S : BitVec 32) {a b : Nat} (h : b + 4 ≤ a ∨ a + 4 ≤ b) (ha : a + 4 ≤ 2 ^ 64)
    (hb : b + 4 ≤ 2 ^ 64) (v : BitVec 32) : (m.writeW (sa S a) v).readW (sa S b) 32 = m.readW (sa S b) 32 :=
  Mem.readW_writeW_sep (VG.Offset.sep _ h hb ha) (by decide)

/-! ## A run's data -/

/-- Where a run's data are: the key schedule `W`, the chaining value `C`, the
`n` blocks at `D` and the working space `S`, of which the run changes the
first 464 bytes. -/
structure Lay (W C D S : BitVec 32) (n : Nat) : Prop where
  hn : 8 * n < 2 ^ 32
  wc : (⟨W.setWidth 64, 384⟩ : Region).Disjoint ⟨C.setWidth 64, 8⟩
  ws : (⟨W.setWidth 64, 384⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  dc : (⟨D.setWidth 64, 8 * n⟩ : Region).Disjoint ⟨C.setWidth 64, 8⟩
  ds : (⟨D.setWidth 64, 8 * n⟩ : Region).Disjoint ⟨S.setWidth 64, 464⟩
  cs : (⟨C.setWidth 64, 8⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  fW : W.toNat + 384 ≤ 2 ^ 32
  fC : C.toNat + 8 ≤ 2 ^ 32
  fD : D.toNat + 8 * n ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32

/-- The regions a run's work reads, and those it writes. -/
abbrev rdN (W D : BitVec 32) (n : Nat) : List Region := [⟨W.setWidth 64, 384⟩, ⟨D.setWidth 64, 8 * n⟩]
abbrev wrN (C S : BitVec 32) : List Region := [⟨C.setWidth 64, 8⟩, ⟨S.setWidth 64, 640⟩]

/-- A state with those regions. -/
def Rg (W C D S : BitVec 32) (n : Nat) (u : State) : Prop := u.rd = rdN W D n ∧ u.wr = wrN C S

namespace Rg
variable {W C D S : BitVec 32} {n : Nat} {u u' : State}

theorem upd (h : Rg W C D S n u) {d : Reg} {v : BitVec 32} (x : Upd u u' d v) : Rg W C D S n u' :=
  ⟨x.rd.trans h.1, x.wr.trans h.2⟩

theorem mupd (h : Rg W C D S n u) {m : Mem} (x : Mupd u u' m) : Rg W C D S n u' :=
  ⟨x.rd.trans h.1, x.wr.trans h.2⟩

theorem ofWr {a : Addr} {k : Nat} (h : InRegions u.wr a k) : InRegions (u.rd ++ u.wr) a k :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem memS (h : Rg W C D S n u) : (⟨S.setWidth 64, 640⟩ : Region) ∈ u.wr := by
  rw [h.2]; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem memW (h : Rg W C D S n u) : (⟨W.setWidth 64, 384⟩ : Region) ∈ u.rd ++ u.wr := by
  rw [h.1]; exact List.mem_append_left _ List.mem_cons_self

theorem inS (h : Rg W C D S n u) {o k : Nat} (hk : o + k ≤ 640) : InRegions u.wr (sa S o) k :=
  ⟨_, h.memS, VG.Offset.contains_base _ hk (by omega_arith)⟩

theorem inS0 (h : Rg W C D S n u) : InRegions u.wr (S.setWidth 64) 4 :=
  ⟨_, h.memS, by simp [Region.Contains]⟩

theorem inC0 (h : Rg W C D S n u) : InRegions u.wr (C.setWidth 64) 4 :=
  ⟨⟨C.setWidth 64, 8⟩, by rw [h.2]; exact List.mem_cons_self, by simp [Region.Contains]⟩

theorem inC4 (h : Rg W C D S n u) : InRegions u.wr (C.setWidth 64 + BitVec.ofNat 64 4) 4 :=
  ⟨⟨C.setWidth 64, 8⟩, by rw [h.2]; exact List.mem_cons_self, VG.Offset.contains_base _ (by decide) (by decide)⟩

theorem inD (h : Rg W C D S n u) {o : Nat} (ho : o + 4 ≤ 8 * n) (hn : 8 * n < 2 ^ 32) :
    InRegions (u.rd ++ u.wr) (D.setWidth 64 + BitVec.ofNat 64 o) 4 :=
  ⟨⟨D.setWidth 64, 8 * n⟩, by rw [h.1]; exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self),
    VG.Offset.contains_base _ ho (by omega_arith)⟩

end Rg

namespace Lay
variable {W C D S : BitVec 32} {n : Nat} (L : Lay W C D S n)
include L

/-- A part of the working space is apart from the chaining value. -/
theorem sc {o l : Nat} (h : o + l ≤ 640) : (⟨sa S o, l⟩ : Region).Disjoint ⟨C.setWidth 64, 8⟩ :=
  L.cs.symm.sub_left (VG.Offset.sub_base _ h)

theorem sc0 {l : Nat} (h : l ≤ 640) : (⟨S.setWidth 64, l⟩ : Region).Disjoint ⟨C.setWidth 64, 8⟩ :=
  L.cs.symm.sub_left (Region.sub_prefix h)

/-- A word of the working space, where the chaining value and the run's slots may change. -/
theorem keepBC {m m' : Mem} (hf : Frame [⟨C.setWidth 64, 8⟩, ⟨sa S 440, 20⟩] m m') {o : Nat}
    (h : o + 4 ≤ 440 ∨ 460 ≤ o) (ho : o + 4 ≤ 640) : m'.readW (sa S o) 32 = m.readW (sa S o) 32 :=
  hf.readW (r := ⟨sa S o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact L.sc ho
    · obtain rfl := List.mem_singleton.mp hr
      exact VG.Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

/-- The block `j` is apart from what a run changes. -/
theorem blk {j : Nat} (hj : j < n) {rs : List Region}
    (hrs : ∀ r ∈ rs, r = ⟨C.setWidth 64, 8⟩ ∨ Region.Sub r ⟨S.setWidth 64, 464⟩) :
    ∀ r ∈ rs, (⟨D.setWidth 64 + BitVec.ofNat 64 (8 * j), 8⟩ : Region).Disjoint r := fun r hr => by
  obtain hsub : Region.Sub ⟨D.setWidth 64 + BitVec.ofNat 64 (8 * j), 8⟩ ⟨D.setWidth 64, 8 * n⟩ :=
    VG.Offset.sub_base _ (by omega_arith)
  rcases hrs r hr with rfl | h
  · exact L.dc.sub_left hsub
  · exact (L.ds.sub_left hsub).sub_right h

end Lay

/-! ## A block -/

/-- A run's work before the block `j`: the block function's buffer ready
(the table's address and the rounds' keys), the registers kept and the run's
three values in their slots, and the chaining value that of the blocks
before. -/
structure LI (W C D S : BitVec 32) (n : Nat) (u₀ : State) (k : Schedule) (c₀ : List Byte) (x1 x2 x3 : BitVec 32)
    (j : Nat) (u : State) : Prop where
  edi : u.gpr sb = S
  esp : u.gpr .esp = u₀.gpr .esp
  rg : Rg W C D S n u
  syms : u.syms = u₀.syms
  tab : u.mem.readW (S.setWidth 64) 32 = u₀.syms tableName
  keys : Keys u.mem S k
  s0 : u.mem.readW (sa S 432) 32 = x1
  s1 : u.mem.readW (sa S 436) 32 = x2
  s2 : u.mem.readW (sa S 440) 32 = x3
  sC : u.mem.readW (sa S 448) 32 = C
  sD : u.mem.readW (sa S 452) 32 = D + BitVec.ofNat 32 (8 * j)
  sN : u.mem.readW (sa S 456) 32 = BitVec.ofNat 32 (n - j)
  frame : Frame [⟨C.setWidth 64, 8⟩, ⟨S.setWidth 64, 464⟩] u₀.mem u.mem
  out : bytesAt u.mem (C.setWidth 64) 8 =
    Spec.Cmac.chain (Spec.Cmac.tdesWith k) c₀ ((Spec.Cmac.blocksAt u₀.mem (D.setWidth 64) 8 n).take j)

/-- A block: exclusive-ored with the chaining value into the buffer,
enciphered there, and stored as the chaining value. -/
theorem body_wp {W C D S : BitVec 32} {n : Nat} (L : Lay W C D S n) {u₀ : State} {k : Schedule} {c₀ : List Byte}
    {x1 x2 x3 : BitVec 32} {j : Nat} (hj : j < n) {u : State} (h : LI W C D S n u₀ k c₀ x1 x2 x3 j u) :
    WP isa chainBody u fun u' => LI W C D S n u₀ k c₀ x1 x2 x3 (j + 1) u' ∧
      eval .ne u' = some (decide (j + 1 < n)) := by
  have fS := L.fS
  have fC := L.fC
  have fD := L.fD
  have hn := L.hn
  show WP isa (.seq (.block chainIn) (.seq crypt (.block chainOut))) u _
  refine WP.seq ?_
  -- the chaining value exclusive-ored with the block, to the buffer's block
  refine ld (a := sa S 448) h.edi (a0 rfl (by omega_arith)) (Rg.ofWr (h.rg.inS (by decide))) fun u₁ v₁ => ?_
  obtain rg₁ := h.rg.upd v₁
  refine ld (a := sa S 452) ((v₁.other _ (by decide)).trans h.edi) (a0 rfl (by omega_arith))
    (Rg.ofWr (rg₁.inS (by decide))) fun u₂ v₂ => ?_
  obtain rg₂ := rg₁.upd v₂
  obtain ecx₂ : u₂.gpr .ecx = C := by rw [v₂.other _ (by decide), v₁.gpr, h.sC]
  obtain esi₂ : u₂.gpr .esi = D + BitVec.ofNat 32 (8 * j) := by rw [v₂.gpr, v₁.mem, h.sD]
  refine ld (a := C.setWidth 64) ecx₂ (az C) (Rg.ofWr rg₂.inC0) fun u₃ v₃ => ?_
  obtain rg₃ := rg₂.upd v₃
  refine ld (a := C.setWidth 64 + BitVec.ofNat 64 4) ((v₃.other _ (by decide)).trans ecx₂)
    (a0 rfl (by omega_arith)) (Rg.ofWr rg₃.inC4) fun u₄ v₄ => ?_
  obtain rg₄ := rg₃.upd v₄
  refine xm (a := D.setWidth 64 + BitVec.ofNat 64 (8 * j))
    ((v₄.other _ (by decide)).trans ((v₃.other _ (by decide)).trans esi₂))
    (addr_add (by omega_arith) (by omega_arith)) (rg₄.inD (by omega_arith) hn) fun u₅ v₅ => ?_
  obtain rg₅ := rg₄.upd v₅
  refine xm (a := D.setWidth 64 + BitVec.ofNat 64 (8 * j + 4))
    ((v₅.other _ (by decide)).trans ((v₄.other _ (by decide)).trans ((v₃.other _ (by decide)).trans esi₂)))
    (addr_add rfl (by omega_arith)) (rg₅.inD (by omega_arith) hn) fun u₆ v₆ => ?_
  obtain rg₆ := rg₅.upd v₆
  obtain edi₆ : u₆.gpr sb = S := by
    rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide)]
    exact h.edi
  refine st (a := sa S 8) edi₆ (a0 rfl (by omega_arith)) (rg₆.inS (by decide)) fun u₇ w₇ => ?_
  obtain rg₇ := rg₆.mupd w₇
  refine st (a := sa S 12) (by rw [w₇.gpr]; exact edi₆) (a0 rfl (by omega_arith)) (rg₇.inS (by decide))
    fun u₈ w₈ => WP.block_nil ?_
  obtain rg₈ := rg₇.mupd w₈
  obtain m₆ : u₆.mem = u.mem := by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  obtain eax₆ : u₆.gpr .eax = u.mem.readW (C.setWidth 64) 32 ^^^
      u.mem.readW (D.setWidth 64 + BitVec.ofNat 64 (8 * j)) 32 := by
    rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.gpr, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  obtain edx₆ : u₆.gpr .edx = u.mem.readW (C.setWidth 64 + BitVec.ofNat 64 4) 32 ^^^
      u.mem.readW (D.setWidth 64 + BitVec.ofNat 64 (8 * j + 4)) 32 := by
    rw [v₆.gpr, v₅.other _ (by decide), v₄.gpr, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  obtain m₈ : u₈.mem = (u.mem.writeW (sa S 8) (u.mem.readW (C.setWidth 64) 32 ^^^
      u.mem.readW (D.setWidth 64 + BitVec.ofNat 64 (8 * j)) 32)).writeW (sa S 12)
      (u.mem.readW (C.setWidth 64 + BitVec.ofNat 64 4) 32 ^^^
        u.mem.readW (D.setWidth 64 + BitVec.ofNat 64 (8 * j + 4)) 32) := by
    rw [w₈.mem, w₇.mem, w₇.gpr, eax₆, edx₆, m₆]
  obtain e12 : sa S 12 = sa S 8 + BitVec.ofNat 64 4 := (VG.Offset.add_add_eq (a := 8) (b := 4) (c := 12) _ rfl).symm
  obtain eD4 : D.setWidth 64 + BitVec.ofNat 64 (8 * j + 4) =
      D.setWidth 64 + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 4 := (VG.Offset.add_add _ _ _).symm
  obtain fA : Frame [⟨sa S 8, 40⟩] u.mem u₈.mem := by
    rw [m₈]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (VG.Offset.contains _ (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (VG.Offset.contains _ (by decide) (by decide) (by decide))
  obtain sy₈ : u₈.syms = u₀.syms := by
    rw [w₈.syms, w₇.syms, v₆.syms, v₅.syms, v₄.syms, v₃.syms, v₂.syms, v₁.syms, h.syms]
  obtain tabOf : ∀ {m : Mem}, Frame [⟨sa S 8, 40⟩] u.mem m → m.readW (S.setWidth 64) 32 = u₀.syms tableName :=
    fun {m} f => (f.readW (r := ⟨S.setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact VG.Offset.base_disjoint _ (by decide) (by decide)) (by decide)).trans h.tab
  obtain keys₈ : Keys u₈.mem S k := keys_frame h.keys fA fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact VG.Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  -- the block, enciphered in place
  refine WP.seq (WP.mono (crypt_blk (N := 640) (by decide) (by rw [w₈.gpr, w₇.gpr]; exact edi₆) rg₈.memS fS
    (by rw [sy₈]; exact tabOf fA) keys₈) fun u₉ ⟨edi₉, esp₉, rd₉, wr₉, sy₉, keys₉, f₉, blk₉⟩ => ?_)
  obtain rg₉ : Rg W C D S n u₉ := ⟨rd₉.trans rg₈.1, wr₉.trans rg₈.2⟩
  obtain fAB : Frame [⟨sa S 8, 40⟩] u.mem u₉.mem := fA.trans f₉
  obtain blkE : bytesAt u₉.mem (sa S 8) 8 =
      VG.Proof.TripleDes.dirCipher .encrypt k (bytesAt u₈.mem (sa S 8) 8) := by exact blk₉
  obtain sl : ∀ o, 48 ≤ o → o + 4 ≤ 640 → u₉.mem.readW (sa S o) 32 = u.mem.readW (sa S o) 32 := fun o h₁ h₂ =>
    slot_keep fAB (.inr (by omega_arith)) (by decide) (by omega_arith)
  -- the buffer's block to the chaining value, and the slots
  refine ld (a := sa S 8) edi₉ (a0 rfl (by omega_arith)) (Rg.ofWr (rg₉.inS (by decide))) fun t₁ y₁ => ?_
  obtain r₁ := rg₉.upd y₁
  obtain e₁ : t₁.gpr sb = S := (y₁.other _ (by decide)).trans edi₉
  refine ld (a := sa S 12) e₁ (a0 rfl (by omega_arith)) (Rg.ofWr (r₁.inS (by decide))) fun t₂ y₂ => ?_
  obtain r₂ := r₁.upd y₂
  obtain e₂ : t₂.gpr sb = S := (y₂.other _ (by decide)).trans e₁
  refine ld (a := sa S 448) e₂ (a0 rfl (by omega_arith)) (Rg.ofWr (r₂.inS (by decide))) fun t₃ y₃ => ?_
  obtain r₃ := r₂.upd y₃
  obtain e₃ : t₃.gpr sb = S := (y₃.other _ (by decide)).trans e₂
  refine ld (a := sa S 452) e₃ (a0 rfl (by omega_arith)) (Rg.ofWr (r₃.inS (by decide))) fun t₄ y₄ => ?_
  obtain r₄ := r₃.upd y₄
  obtain e₄ : t₄.gpr sb = S := (y₄.other _ (by decide)).trans e₃
  refine ld (a := sa S 456) e₄ (a0 rfl (by omega_arith)) (Rg.ofWr (r₄.inS (by decide))) fun t₅ y₅ => ?_
  obtain r₅ := r₄.upd y₅
  obtain e₅ : t₅.gpr sb = S := (y₅.other _ (by decide)).trans e₄
  refine ld (a := sa S 440) e₅ (a0 rfl (by omega_arith)) (Rg.ofWr (r₅.inS (by decide))) fun t₆ y₆ => ?_
  obtain r₆ := r₅.upd y₆
  obtain e₆ : t₆.gpr sb = S := (y₆.other _ (by decide)).trans e₅
  obtain mt₆ : t₆.mem = u₉.mem := by rw [y₆.mem, y₅.mem, y₄.mem, y₃.mem, y₂.mem, y₁.mem]
  obtain eax' : t₆.gpr .eax = u₉.mem.readW (sa S 8) 32 := by
    rw [y₆.other _ (by decide), y₅.other _ (by decide), y₄.other _ (by decide), y₃.other _ (by decide),
      y₂.other _ (by decide), y₁.gpr]
  obtain edx' : t₆.gpr .edx = u₉.mem.readW (sa S 12) 32 := by
    rw [y₆.other _ (by decide), y₅.other _ (by decide), y₄.other _ (by decide), y₃.other _ (by decide), y₂.gpr,
      y₁.mem]
  obtain ecx' : t₆.gpr .ecx = C := by
    rw [y₆.other _ (by decide), y₅.other _ (by decide), y₄.other _ (by decide), y₃.gpr, y₂.mem, y₁.mem,
      sl 448 (by decide) (by decide), h.sC]
  obtain esi' : t₆.gpr .esi = D + BitVec.ofNat 32 (8 * j) := by
    rw [y₆.other _ (by decide), y₅.other _ (by decide), y₄.gpr, y₃.mem, y₂.mem, y₁.mem,
      sl 452 (by decide) (by decide), h.sD]
  obtain ebp' : t₆.gpr .ebp = BitVec.ofNat 32 (n - j) := by
    rw [y₆.other _ (by decide), y₅.gpr, y₄.mem, y₃.mem, y₂.mem, y₁.mem, sl 456 (by decide) (by decide), h.sN]
  obtain ebx' : t₆.gpr .ebx = x3 := by
    rw [y₆.gpr, y₅.mem, y₄.mem, y₃.mem, y₂.mem, y₁.mem, sl 440 (by decide) (by decide), h.s2]
  refine st (a := C.setWidth 64) ecx' (az C) r₆.inC0 fun t₇ z₇ => ?_
  obtain r₇ := r₆.mupd z₇
  refine st (a := C.setWidth 64 + BitVec.ofNat 64 4) (by rw [z₇.gpr]; exact ecx') (a0 rfl (by omega_arith)) r₇.inC4
    fun t₈ z₈ => ?_
  obtain r₈ := r₇.mupd z₈
  obtain g₈ : t₈.gpr = t₆.gpr := by rw [z₈.gpr, z₇.gpr]
  refine wp_addi fun t₉ y₉ => ?_
  obtain r₉ := r₈.upd y₉
  obtain e₉ : t₉.gpr sb = S := by rw [y₉.other _ (by decide), g₈]; exact e₆
  refine st (a := sa S 448) e₉ (a0 rfl (by omega_arith)) (r₉.inS (by decide)) fun t₁₀ z₁₀ => ?_
  obtain r₁₀ := r₉.mupd z₁₀
  refine st (a := sa S 452) (by rw [z₁₀.gpr]; exact e₉) (a0 rfl (by omega_arith)) (r₁₀.inS (by decide))
    fun t₁₁ z₁₁ => ?_
  obtain r₁₁ := r₁₀.mupd z₁₁
  refine st (a := sa S 440) (by rw [z₁₁.gpr, z₁₀.gpr]; exact e₉) (a0 rfl (by omega_arith)) (r₁₁.inS (by decide))
    fun t₁₂ z₁₂ => ?_
  obtain r₁₂ := r₁₁.mupd z₁₂
  obtain g₁₂ : t₁₂.gpr = t₉.gpr := by rw [z₁₂.gpr, z₁₁.gpr, z₁₀.gpr]
  refine wp_subi fun t₁₃ y₁₃ _ zf₁₃ => ?_
  obtain r₁₃ := r₁₂.upd y₁₃
  obtain e₁₃ : t₁₃.gpr sb = S := by rw [y₁₃.other _ (by decide), g₁₂]; exact e₉
  refine st (a := sa S 456) e₁₃ (a0 rfl (by omega_arith)) (r₁₃.inS (by decide)) fun t₁₄ z₁₄ => WP.block_nil ?_
  obtain r₁₄ := r₁₃.mupd z₁₄
  -- the values stored
  obtain v8 : t₇.gpr .edx = u₉.mem.readW (sa S 12) 32 := by rw [z₇.gpr]; exact edx'
  obtain v10 : t₉.gpr .ecx = C := by rw [y₉.other _ (by decide), g₈]; exact ecx'
  obtain v11 : t₁₀.gpr .esi = D + BitVec.ofNat 32 (8 * (j + 1)) := by
    rw [z₁₀.gpr, y₉.gpr, g₈, esi', show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, VG.Offset.add_add,
      show 8 * j + 8 = 8 * (j + 1) by omega_arith]
  obtain v12 : t₁₁.gpr .ebx = x3 := by rw [z₁₁.gpr, z₁₀.gpr, y₉.other _ (by decide), g₈]; exact ebx'
  obtain ebp₁₂ : t₁₂.gpr .ebp = BitVec.ofNat 32 (n - j) := by rw [g₁₂, y₉.other _ (by decide), g₈]; exact ebp'
  obtain v14 : t₁₃.gpr .ebp = BitVec.ofNat 32 (n - (j + 1)) := by
    rw [y₁₃.gpr, ebp₁₂, ofNat_pred (by omega_arith)]
    exact congrArg (BitVec.ofNat 32) (by omega_arith)
  obtain mF : t₁₄.mem = ((((((u₉.mem.writeW (C.setWidth 64) (u₉.mem.readW (sa S 8) 32)).writeW
      (C.setWidth 64 + BitVec.ofNat 64 4) (u₉.mem.readW (sa S 12) 32)).writeW (sa S 448) C).writeW (sa S 452)
      (D + BitVec.ofNat 32 (8 * (j + 1)))).writeW (sa S 440) x3).writeW (sa S 456)
      (BitVec.ofNat 32 (n - (j + 1)))) := by
    rw [z₁₄.mem, v14, y₁₃.mem, z₁₂.mem, v12, z₁₁.mem, v11, z₁₀.mem, v10, y₉.mem, z₈.mem, v8, z₇.mem, eax', mt₆]
  obtain cs : ∀ o, 440 ≤ o → o + 4 ≤ 460 → (⟨sa S 440, 20⟩ : Region).Contains (sa S o) (32 / 8) := fun o h₁ h₂ =>
    VG.Offset.contains _ h₁ (by omega_arith) (by decide)
  obtain fS4 : Frame [⟨sa S 440, 20⟩] ((u₉.mem.writeW (C.setWidth 64) (u₉.mem.readW (sa S 8) 32)).writeW
      (C.setWidth 64 + BitVec.ofNat 64 4) (u₉.mem.readW (sa S 12) 32)) t₁₄.mem := by
    rw [mF]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cs 448 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cs 452 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (cs 440 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (cs 456 (by decide) (by decide))
  obtain fBC : Frame [⟨C.setWidth 64, 8⟩, ⟨sa S 440, 20⟩] u₉.mem t₁₄.mem :=
    (((Frame.refl _ _).writeW List.mem_cons_self _ (by simp [Region.Contains])).writeW List.mem_cons_self _
      (VG.Offset.contains_base _ (by decide) (by decide))).trans
      (fS4.mono fun r hr => List.mem_cons_of_mem _ hr)
  refine ⟨⟨?_, ?_, r₁₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [z₁₄.gpr]; exact e₁₃
  · rw [z₁₄.gpr, y₁₃.other _ (by decide), g₁₂, y₉.other _ (by decide), g₈, y₆.other _ (by decide),
      y₅.other _ (by decide), y₄.other _ (by decide), y₃.other _ (by decide), y₂.other _ (by decide),
      y₁.other _ (by decide), esp₉, w₈.gpr, w₇.gpr, v₆.other _ (by decide), v₅.other _ (by decide),
      v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide)]
    exact h.esp
  · rw [z₁₄.syms, y₁₃.syms, z₁₂.syms, z₁₁.syms, z₁₀.syms, y₉.syms, z₈.syms, z₇.syms, y₆.syms, y₅.syms, y₄.syms,
      y₃.syms, y₂.syms, y₁.syms, sy₉, sy₈]
  · exact (fBC.readW (r := ⟨S.setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact L.sc0 (by decide)
      · obtain rfl := List.mem_singleton.mp hr
        exact VG.Offset.base_disjoint _ (by decide) (by decide)) (by decide)).trans (tabOf fAB)
  · exact keys_frame keys₉ fBC fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact L.sc (by decide)
      · obtain rfl := List.mem_singleton.mp hr
        exact VG.Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  · exact (L.keepBC fBC (.inl (by decide)) (by decide)).trans ((sl 432 (by decide) (by decide)).trans h.s0)
  · exact (L.keepBC fBC (.inl (by decide)) (by decide)).trans ((sl 436 (by decide) (by decide)).trans h.s1)
  · rw [mF, rds _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [mF, rds _ _ (by decide) (by decide) (by decide), rds _ _ (by decide) (by decide) (by decide),
      rds _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [mF, rds _ _ (by decide) (by decide) (by decide), rds _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [mF, Mem.readW_writeW_self32]
  · refine (h.frame.trans (fAB.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)).trans
      (fBC.sub fun r hr => ?_)
    · obtain rfl := List.mem_singleton.mp hr
      exact VG.Offset.sub_base _ (by decide)
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · obtain rfl := List.mem_singleton.mp hr
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, VG.Offset.sub_base _ (by decide)⟩
  · rw [bytesAt_frame fS4 (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact (L.sc (by decide)).symm) (by decide), pair_le8 _ rfl rfl, le8_pair u₉.mem rfl e12, blkE, m₈,
      pair_le8 _ rfl e12, ← BitVec.xor_append, le8_xor, le8_pair u.mem rfl rfl, le8_pair u.mem rfl eD4, h.out,
      bytesAt_frame h.frame (L.blk hj fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact .inl rfl
        · obtain rfl := List.mem_singleton.mp hr
          exact .inr fun _ h => h) (by decide), take_succ_blocks _ _ hj, chain_append, chain_single]
    exact congrFun (tdesWith_eq k).symm _
  · show t₁₄.zf.map (!·) = _
    rw [z₁₄.zf, zf₁₃, ebp₁₂, ofNat_pred (by omega_arith), ofNat_beq_zero (by omega_arith)]
    simp only [Option.map_some, Option.some.injEq]
    by_cases h7 : j + 1 < n <;> simp [h7] <;> omega_arith

/-! ## A run's work -/

/-- A run's work, in a state with its regions: the keys, the blocks, and the
registers back. -/
theorem chainRun_wp {W C D S : BitVec 32} {n : Nat} (L : Lay W C D S n) (hn : 0 < n) {u : State}
    {x1 x2 x3 : BitVec 32} (rg : Rg W C D S n u) (eax : u.gpr .eax = u.syms tableName) (ebp : u.gpr .ebp = W)
    (edi : u.gpr sb = S) (s0 : u.mem.readW (sa S 432) 32 = x1) (s1 : u.mem.readW (sa S 436) 32 = x2)
    (s2 : u.mem.readW (sa S 440) 32 = x3) (sC : u.mem.readW (sa S 448) 32 = C)
    (sD : u.mem.readW (sa S 452) 32 = D) (sN : u.mem.readW (sa S 456) 32 = BitVec.ofNat 32 n) :
    WP isa chainRun u fun u' => u'.gpr .ebx = x1 ∧ u'.gpr .esi = x2 ∧ u'.gpr .ebp = x3 ∧ u'.gpr sb = S ∧
      u'.gpr .esp = u.gpr .esp ∧ Rg W C D S n u' ∧
      Frame [⟨C.setWidth 64, 8⟩, ⟨S.setWidth 64, 464⟩] u.mem u'.mem ∧
      bytesAt u'.mem (C.setWidth 64) 8 = Spec.Cmac.chain (ciphAt u.mem (W.setWidth 64))
        (bytesAt u.mem (C.setWidth 64) 8) (Spec.Cmac.blocksAt u.mem (D.setWidth 64) 8 n) := by
  have fS := L.fS
  show WP isa (.seq (.block (.store (at_ sb 0) .eax :: .mov .eax (.reg .ebp) :: .mov .esi (.reg sb) :: keys))
    (.seq (.loop chainBody .ne) (.block chainRestore))) u _
  refine WP.seq ?_
  refine st (a := S.setWidth 64) edi (az S) rg.inS0 fun u₁ w₁ => wp_mov fun u₂ v₂ => wp_mov fun u₃ v₃ => ?_
  obtain rg₃ : Rg W C D S n u₃ := ((rg.mupd w₁).upd v₂).upd v₃
  obtain m₃ : u₃.mem = u.mem.writeW (S.setWidth 64) (u.syms tableName) := by rw [v₃.mem, v₂.mem, w₁.mem, eax]
  obtain f₃ : Frame [⟨S.setWidth 64, 432⟩] u.mem u₃.mem := by
    rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by simp [Region.Contains])
  obtain eax₃ : u₃.gpr .eax = W := by rw [v₃.other _ (by decide), v₂.gpr, w₁.gpr]; exact ebp
  obtain esi₃ : u₃.gpr .esi = S := by rw [v₃.gpr, v₂.other _ (by decide), w₁.gpr]; exact edi
  obtain ek : keys = (List.range' 0 16).flatMap keys3 ++ [] := by rw [List.append_nil]; exact keys_eq
  rw [ek]
  refine keysFrom_wp (k := Spec.TripleDes.scheduleAt u.mem (W.setWidth 64)) (N := 640) eax₃ esi₃ rg₃.memW
    (by decide) rg₃.memS L.ws L.fW L.fS (fun i hi => ?_) (fun u₄ h₄ => WP.block_nil ?_) 16 0 u₃ rfl
    ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun i _ h => absurd h (Nat.not_lt_zero _)⟩
  · rw [VG.Proof.TripleDes.vector_getD _ i hi, VG.Proof.TripleDes.scheduleAt_readW _ _ i hi]
    exact f₃.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (L.ws.sub_left (VG.Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by decide)))
      (by decide)
  -- the buffer is ready
  obtain f₄ : Frame [⟨S.setWidth 64, 432⟩] u.mem u₄.mem := f₃.trans (h₄.frame.sub fun r hr =>
    ⟨_, List.mem_singleton_self _, by
      obtain rfl := List.mem_singleton.mp hr
      exact VG.Offset.sub_base _ (by decide)⟩)
  obtain rg₄ : Rg W C D S n u₄ := ⟨h₄.rd.trans rg₃.1, h₄.wr.trans rg₃.2⟩
  obtain edi₄ : u₄.gpr sb = S := by
    rw [h₄.gpr _ (by decide) (by decide), v₃.other _ (by decide), v₂.other _ (by decide), w₁.gpr]; exact edi
  obtain sy₄ : u₄.syms = u.syms := by rw [h₄.syms, v₃.syms, v₂.syms, w₁.syms]
  obtain tab₄ : u₄.mem.readW (S.setWidth 64) 32 = u₄.syms tableName := by
    rw [sy₄, h₄.frame.readW (r := ⟨S.setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact VG.Offset.base_disjoint _ (by decide) (by decide)) (by decide), m₃]
    exact Mem.readW_writeW_self32 _ _ _
  obtain slot : ∀ o, 432 ≤ o → o + 4 ≤ 640 → u₄.mem.readW (sa S o) 32 = u.mem.readW (sa S o) 32 :=
    fun o h₁ h₂ => slot_keep0 f₄ h₁ (by omega_arith)
  obtain eb : Spec.Cmac.blocksAt u₄.mem (D.setWidth 64) 8 n = Spec.Cmac.blocksAt u.mem (D.setWidth 64) 8 n := by
    simp only [Spec.Cmac.blocksAt]
    refine List.map_congr_left fun i hi => bytesAt_frame f₄ (L.blk (List.mem_range.mp hi) fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact .inr (Region.sub_prefix (by decide))) (by decide)
  refine WP.seq (WP.mono (count_loop (I := LI W C D S n u₄ (Spec.TripleDes.scheduleAt u.mem (W.setWidth 64))
      (bytesAt u₄.mem (C.setWidth 64) 8) x1 x2 x3) hn
    ⟨edi₄, rfl, rg₄, rfl, tab₄, fun i hi => h₄.done i hi (by omega_arith),
      (slot 432 (by decide) (by decide)).trans s0, (slot 436 (by decide) (by decide)).trans s1,
      (slot 440 (by decide) (by decide)).trans s2, (slot 448 (by decide) (by decide)).trans sC,
      by rw [slot 452 (by decide) (by decide), sD]; simp, (slot 456 (by decide) (by decide)).trans sN,
      Frame.refl _ _, by rw [List.take_zero]; rfl⟩
    fun t u' ht hI => body_wp L ht hI) fun u₅ h₅ => ?_)
  -- the registers back
  obtain rg₅ := h₅.rg
  refine ld (a := sa S 432) h₅.edi (a0 rfl (by omega_arith)) (Rg.ofWr (rg₅.inS (by decide))) fun u₆ v₆ => ?_
  obtain rg₆ := rg₅.upd v₆
  refine ld (a := sa S 436) ((v₆.other _ (by decide)).trans h₅.edi) (a0 rfl (by omega_arith))
    (Rg.ofWr (rg₆.inS (by decide))) fun u₇ v₇ => ?_
  obtain rg₇ := rg₆.upd v₇
  refine ld (a := sa S 440) ((v₇.other _ (by decide)).trans ((v₆.other _ (by decide)).trans h₅.edi))
    (a0 rfl (by omega_arith)) (Rg.ofWr (rg₇.inS (by decide))) fun u₈ v₈ => WP.block_nil ?_
  obtain m₈ : u₈.mem = u₅.mem := by rw [v₈.mem, v₇.mem, v₆.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, rg₇.upd v₈, ?_, ?_⟩
  · rw [v₈.other _ (by decide), v₇.other _ (by decide), v₆.gpr]; exact h₅.s0
  · rw [v₈.other _ (by decide), v₇.gpr, v₆.mem]; exact h₅.s1
  · rw [v₈.gpr, v₇.mem, v₆.mem]; exact h₅.s2
  · rw [v₈.other _ (by decide), v₇.other _ (by decide), v₆.other _ (by decide)]; exact h₅.edi
  · rw [v₈.other _ (by decide), v₇.other _ (by decide), v₆.other _ (by decide), h₅.esp,
      h₄.gpr _ (by decide) (by decide), v₃.other _ (by decide), v₂.other _ (by decide), w₁.gpr]
  · rw [m₈]
    exact (f₄.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
      obtain rfl := List.mem_singleton.mp hr
      exact Region.sub_prefix (by decide)⟩).trans h₅.frame
  · rw [m₈, h₅.out, List.take_of_length_le (by simp [Spec.Cmac.blocksAt]), eb,
      bytesAt_frame f₄ (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact (L.sc0 (by decide)).symm) (by decide)]

/-! ## The function that chains blocks -/

/-- The return address's slot is apart from the four bytes below it. -/
theorem ret_disjoint {sp : BitVec 32} (low : 8 ≤ sp.toNat) :
    Region.Disjoint (below sp 4) (below (sp - 4) 4) := by
  have hsp := sp.isLt
  obtain e4 : (sp - BitVec.ofNat 32 4).setWidth 64 = (sp - BitVec.ofNat 32 8).setWidth 64 + BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [low, hsp]
  obtain e8 : (sp - 4 - BitVec.ofNat 32 4).setWidth 64 =
      (sp - BitVec.ofNat 32 8).setWidth 64 + BitVec.ofNat 64 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [low, hsp]
  generalize (sp - BitVec.ofNat 32 8).setWidth 64 = X at e4 e8
  obtain b4 : below sp 4 = ⟨X + BitVec.ofNat 64 4, 4⟩ := by simp only [below]; rw [e4]
  obtain b4' : below (sp - 4) 4 = ⟨X + BitVec.ofNat 64 0, 4⟩ := by simp only [below]; rw [e8]
  rw [b4, b4']
  exact VG.Offset.disjoint X (by decide) (by decide) (by decide)

/-- What the function needs: the key schedule `W`, the chaining value `C`,
`n` blocks at `D` and the working space `S`, in `eax`, `edx`, `ebx`, `esi`
and `edi`, and eight bytes of stack. The blocks may be in the working space
after its first 464 bytes. -/
structure CArgs (s : State) (W C D S : BitVec 32) (n : Nat) : Prop where
  eax : s.gpr .eax = W
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = D
  esi : s.gpr .esi = BitVec.ofNat 32 n
  edi : s.gpr sb = S
  esp : 8 ≤ (s.gpr .esp).toNat
  lay : Lay W C D S n
  bW : (below (s.gpr .esp) 8).Disjoint ⟨W.setWidth 64, 384⟩
  bD : (below (s.gpr .esp) 8).Disjoint ⟨D.setWidth 64, 8 * n⟩
  bC : (below (s.gpr .esp) 8).Disjoint ⟨C.setWidth 64, 8⟩
  bS : (below (s.gpr .esp) 8).Disjoint ⟨S.setWidth 64, 640⟩
  reads : Covers (rdN W D n) (s.rd ++ s.wr)
  writes : Covers (wrN C S) s.wr

/-- What the function leaves: the chaining value after the blocks; of memory
it changes that, the first 464 bytes of the working space and eight bytes of
stack. -/
structure CPost (s : State) (W C D S : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C.setWidth 64, 8⟩, ⟨S.setWidth 64, 464⟩, below (s.gpr .esp) 8] s.mem s'.mem
  out : bytesAt s'.mem (C.setWidth 64) 8 = Spec.Cmac.chain (ciphAt s.mem (W.setWidth 64))
    (bytesAt s.mem (C.setWidth 64) 8) (Spec.Cmac.blocksAt s.mem (D.setWidth 64) 8 n)

open VG.Proof.CmacTripleDes.X86 (scheduleAt_frame) in
/-- **The function's call.** -/
theorem chain_wp {s : State} {W C D S : BitVec 32} {n : Nat} (h : CArgs s W C D S n) :
    WP isa run s (CPost s W C D S n) := by
  have hsp := h.esp
  have L := h.lay
  have fS := L.fS
  have hn8 := L.hn
  obtain cm : s.callEntry.mem = s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0) := State.callEntry_mem s
  obtain esp' : s.callEntry.gpr .esp = s.gpr .esp - 4 := State.callEntry_esp s
  obtain fc : Frame [below (s.gpr .esp) 8] s.mem s.callEntry.mem := by
    rw [cm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_top (by decide) hsp (by decide))
  obtain r4 : Region.Sub (below (s.gpr .esp) 4) (below (s.gpr .esp) 8) := below_sub (by decide) hsp
  obtain r8 : Region.Sub (below (s.gpr .esp - 4) 4) (below (s.gpr .esp) 8) :=
    below_inner (a := 4) (k := 4) (by decide) hsp
  obtain G : ∀ r, r ≠ .esp → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  refine WP.callBody ?_
  show WP isa (.seq (.block ([.alu .cmp .esi (.imm 0)] : List Instr)) (.ite .e (.block [])
    (.seq (.block chainSave) (.seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1)) chainRun))))
    s.callEntry _
  refine WP.seq (wp_cmpi fun t₁ f₁ _ z₁ => WP.block_nil ?_)
  obtain ev : isa.eval .e t₁ = some (decide (n = 0)) := by
    show t₁.zf = _
    rw [z₁, G _ (by decide), h.esi, show BitVec.ofNat 32 n - 0 = BitVec.ofNat 32 n by simp,
      ofNat_beq_zero (by omega_arith)]
  by_cases h0 : n = 0
  · -- no blocks
    subst h0
    refine WP.ite true (by rw [ev]; simp) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    obtain U := Upd.setReg t₁ .esp (s.gpr .esp)
    refine ⟨by rw [f₁.gpr]; exact esp', by rw [f₁.mem, cm]; exact Mem.readW_writeW_self32 _ _ _,
      U.rd.trans f₁.rd, U.wr.trans f₁.wr, fun r _ => ?_, ?_, ?_⟩
    · by_cases he : r = .esp
      · rw [he]; exact U.gpr
      · rw [U.other r he, f₁.gpr]; exact G r he
    · rw [U.mem, f₁.mem]
      exact fc.mono fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · rw [U.mem, f₁.mem, bytesAt_frame fc (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact h.bC.symm) (by decide)]
      rfl
  -- the registers and the arguments to their slots
  refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => WP.seq ?_
  obtain wS : ∀ {t : State}, t.wr = s.wr → ∀ o, o + 4 ≤ 640 → InRegions t.wr (sa S o) 4 := fun {t} ht o ho => by
    rw [ht]
    exact h.writes _ _ ⟨⟨S.setWidth 64, 640⟩, List.mem_cons_of_mem _ List.mem_cons_self,
      VG.Offset.contains_base _ ho (by omega_arith)⟩
  obtain edi₁ : t₁.gpr sb = S := by rw [f₁.gpr, G _ (by decide)]; exact h.edi
  obtain wr₁ : t₁.wr = s.wr := f₁.wr
  refine st (a := sa S 432) edi₁ (a0 rfl (by omega_arith)) (wS wr₁ 432 (by decide)) fun t₂ z₂ => ?_
  obtain wr₂ : t₂.wr = s.wr := z₂.wr.trans wr₁
  refine st (a := sa S 436) (by rw [z₂.gpr]; exact edi₁) (a0 rfl (by omega_arith)) (wS wr₂ 436 (by decide))
    fun t₃ z₃ => ?_
  obtain wr₃ : t₃.wr = s.wr := z₃.wr.trans wr₂
  refine st (a := sa S 440) (by rw [z₃.gpr, z₂.gpr]; exact edi₁) (a0 rfl (by omega_arith)) (wS wr₃ 440 (by decide))
    fun t₄ z₄ => ?_
  obtain wr₄ : t₄.wr = s.wr := z₄.wr.trans wr₃
  refine st (a := sa S 448) (by rw [z₄.gpr, z₃.gpr, z₂.gpr]; exact edi₁) (a0 rfl (by omega_arith))
    (wS wr₄ 448 (by decide)) fun t₅ z₅ => ?_
  obtain wr₅ : t₅.wr = s.wr := z₅.wr.trans wr₄
  refine st (a := sa S 452) (by rw [z₅.gpr, z₄.gpr, z₃.gpr, z₂.gpr]; exact edi₁) (a0 rfl (by omega_arith))
    (wS wr₅ 452 (by decide)) fun t₆ z₆ => ?_
  obtain wr₆ : t₆.wr = s.wr := z₆.wr.trans wr₅
  refine st (a := sa S 456) (by rw [z₆.gpr, z₅.gpr, z₄.gpr, z₃.gpr, z₂.gpr]; exact edi₁) (a0 rfl (by omega_arith))
    (wS wr₆ 456 (by decide)) fun t₇ z₇ => wp_mov fun t₈ y₈ => WP.block_nil ?_
  obtain g₇ : t₇.gpr = s.callEntry.gpr := by rw [z₇.gpr, z₆.gpr, z₅.gpr, z₄.gpr, z₃.gpr, z₂.gpr, f₁.gpr]
  obtain m₈ : t₈.mem = ((((((s.callEntry.mem.writeW (sa S 432) D).writeW (sa S 436) (BitVec.ofNat 32 n)).writeW
      (sa S 440) (s.gpr .ebp)).writeW (sa S 448) C).writeW (sa S 452) D).writeW (sa S 456)
      (BitVec.ofNat 32 n)) := by
    rw [y₈.mem, z₇.mem, z₆.mem, z₅.mem, z₄.mem, z₃.mem, z₂.mem, z₆.gpr, z₅.gpr, z₄.gpr, z₃.gpr, z₂.gpr, f₁.gpr,
      f₁.mem, G .esi (by decide), G .ebx (by decide), G .edx (by decide), G .ebp (by decide), h.esi, h.ebx, h.edx]
  obtain cS : ∀ o, o + 4 ≤ 464 → (⟨S.setWidth 64, 464⟩ : Region).Contains (sa S o) (32 / 8) := fun o ho =>
    VG.Offset.contains_base _ ho (by omega_arith)
  obtain fSv : Frame [⟨S.setWidth 64, 464⟩] s.callEntry.mem t₈.mem := by
    rw [m₈]
    exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cS 432 (by decide))).writeW
      (List.mem_singleton_self _) _ (cS 436 (by decide))).writeW (List.mem_singleton_self _) _
      (cS 440 (by decide))).writeW (List.mem_singleton_self _) _ (cS 448 (by decide))).writeW
      (List.mem_singleton_self _) _ (cS 452 (by decide))).writeW (List.mem_singleton_self _) _ (cS 456 (by decide))
  obtain esp₈ : t₈.gpr .esp = s.gpr .esp - 4 := by rw [y₈.other _ (by decide), g₇]; exact esp'
  -- the table's address
  refine WP.seq (WP.mono (symFrame_ok tableName t₈ (by
    rw [esp₈, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.X86.sub_toNat (by omega_arith)]
    omega_arith)) fun t₉ h₉ => ?_)
  obtain f₉ : Frame [below (s.gpr .esp - 4) 4] t₈.mem t₉.mem := by rw [← esp₈]; exact h₉.frame
  obtain dS9 : ∀ o, o + 4 ≤ 640 → (⟨sa S o, 4⟩ : Region).Disjoint (below (s.gpr .esp - 4) 4) := fun o ho =>
    ((h.bS.sub_left r8).symm).sub_left (VG.Offset.sub_base _ ho)
  obtain sl9 : ∀ o, o + 4 ≤ 640 → t₉.mem.readW (sa S o) 32 = t₈.mem.readW (sa S o) 32 := fun o ho =>
    f₉.readW (r := ⟨sa S o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact dS9 o ho) (by decide)
  obtain rd₉ : t₉.rd = s.rd := by rw [h₉.rd, y₈.rd, z₇.rd, z₆.rd, z₅.rd, z₄.rd, z₃.rd, z₂.rd, f₁.rd]; rfl
  obtain wr₉ : t₉.wr = s.wr := by rw [h₉.wr, y₈.wr]; exact z₇.wr.trans wr₆
  obtain g₉ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebp → r ≠ .esp → t₉.gpr r = s.gpr r := fun r a b c d => by
    rw [h₉.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨a, b⟩),
      y₈.other r c, g₇]
    exact G r d
  -- the run's work, with the regions it uses
  refine WP.narrow (rd := rdN W D n) (wr := wrN C S) (chainRun_wp L (Nat.pos_of_ne_zero h0)
      (u := t₉.withRegions (rdN W D n) (wrN C S)) (x1 := D) (x2 := BitVec.ofNat 32 n) (x3 := s.gpr .ebp) ⟨rfl, rfl⟩
      (h₉.addr.trans (congrFun h₉.syms.symm tableName)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    (by rw [rd₉, wr₉]; exact Covers.append_left h.reads (Covers.right h.writes)) (by rw [wr₉]; exact h.writes)
    (fun u' hrd hwr _ ⟨ebx', esi', ebp', edi', espx, _, fr', out'⟩ => ?_) (by lit_decide)
  · show t₉.gpr .ebp = W
    rw [h₉.gpr _ (by decide), y₈.gpr, g₇, G _ (by decide)]; exact h.eax
  · show t₉.gpr sb = S
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide)]; exact h.edi
  · show t₉.mem.readW (sa S 432) 32 = D
    rw [sl9 432 (by decide), m₈, rds _ _ (by decide) (by decide) (by decide),
      rds _ _ (by decide) (by decide) (by decide), rds _ _ (by decide) (by decide) (by decide),
      rds _ _ (by decide) (by decide) (by decide), rds _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · show t₉.mem.readW (sa S 436) 32 = BitVec.ofNat 32 n
    rw [sl9 436 (by decide), m₈, rds _ _ (by decide) (by decide) (by decide),
      rds _ _ (by decide) (by decide) (by decide), rds _ _ (by decide) (by decide) (by decide),
      rds _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · show t₉.mem.readW (sa S 440) 32 = s.gpr .ebp
    rw [sl9 440 (by decide), m₈, rds _ _ (by decide) (by decide) (by decide),
      rds _ _ (by decide) (by decide) (by decide), rds _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · show t₉.mem.readW (sa S 448) 32 = C
    rw [sl9 448 (by decide), m₈, rds _ _ (by decide) (by decide) (by decide),
      rds _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · show t₉.mem.readW (sa S 452) 32 = D
    rw [sl9 452 (by decide), m₈, rds _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · show t₉.mem.readW (sa S 456) 32 = BitVec.ofNat 32 n
    rw [sl9 456 (by decide), m₈, Mem.readW_writeW_self32]
  -- what the call leaves
  obtain ebx' : u'.gpr .ebx = D := ebx'
  obtain esi' : u'.gpr .esi = BitVec.ofNat 32 n := esi'
  obtain ebp' : u'.gpr .ebp = s.gpr .ebp := ebp'
  obtain edi' : u'.gpr sb = S := edi'
  obtain espx : u'.gpr .esp = t₉.gpr .esp := espx
  obtain fr' : Frame [⟨C.setWidth 64, 8⟩, ⟨S.setWidth 64, 464⟩] t₉.mem u'.mem := fr'
  obtain out' : bytesAt u'.mem (C.setWidth 64) 8 = Spec.Cmac.chain (ciphAt t₉.mem (W.setWidth 64))
    (bytesAt t₉.mem (C.setWidth 64) 8) (Spec.Cmac.blocksAt t₉.mem (D.setWidth 64) 8 n) := out'
  obtain esp₉ : t₉.gpr .esp = s.gpr .esp - 4 := (h₉.gpr _ (by decide)).trans esp₈
  -- memory from the function's entry to the run's work, and to its end
  obtain F9 : Frame [⟨S.setWidth 64, 464⟩, below (s.gpr .esp - 4) 4] s.callEntry.mem t₉.mem :=
    (fSv.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self).trans
    (f₉.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  obtain F : Frame [⟨C.setWidth 64, 8⟩, ⟨S.setWidth 64, 464⟩, below (s.gpr .esp - 4) 4] s.callEntry.mem u'.mem :=
    (F9.mono fun r hr => List.mem_cons_of_mem _ hr).trans (fr'.mono fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  obtain G9 : Frame [⟨S.setWidth 64, 464⟩, below (s.gpr .esp) 8] s.mem t₉.mem :=
    (fc.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ List.mem_cons_self).trans
    (F9.sub fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, r8⟩)
  obtain U := Upd.setReg u' .esp (s.gpr .esp)
  refine ⟨espx.trans esp₉, ?_, U.rd.trans (hrd.trans rd₉), U.wr.trans (hwr.trans wr₉), fun r hr => ?_, ?_, ?_⟩
  · -- the return address is where the call put it
    rw [F.readW (r := below (s.gpr .esp) 4) (Region.contains_self _ _) (fun r hr => ?_) (by decide), cm]
    · exact Mem.readW_writeW_self32 _ _ _
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact h.bC.sub_left r4
      rcases List.mem_cons.mp hr with rfl | hr
      · exact (h.bS.sub_left r4).sub_right (Region.sub_prefix (by decide))
      · rw [List.mem_singleton.mp hr]; exact ret_disjoint hsp
  · by_cases he : r = .esp
    · rw [he]; exact U.gpr
    rw [U.other r he]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ebx'.trans h.ebx.symm
    · exact esi'.trans h.esi.symm
    · exact edi'.trans h.edi.symm
    · exact ebp'
    · exact absurd rfl he
  · rw [U.mem]
    exact (fc.mono fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)).trans
      (F.sub fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
        · rw [List.mem_singleton.mp hr]
          exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), r8⟩)
  · obtain eK : ciphAt t₉.mem (W.setWidth 64) = ciphAt s.mem (W.setWidth 64) :=
      congrArg Spec.Cmac.tdesWith (scheduleAt_frame G9 fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact L.ws.sub_right (Region.sub_prefix (by decide))
        · rw [List.mem_singleton.mp hr]; exact h.bW.symm)
    obtain eC : bytesAt t₉.mem (C.setWidth 64) 8 = bytesAt s.mem (C.setWidth 64) 8 :=
      bytesAt_frame G9 (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact L.cs.sub_right (Region.sub_prefix (by decide))
        · rw [List.mem_singleton.mp hr]; exact h.bC.symm) (by decide)
    obtain eB : Spec.Cmac.blocksAt t₉.mem (D.setWidth 64) 8 n = Spec.Cmac.blocksAt s.mem (D.setWidth 64) 8 n := by
      simp only [Spec.Cmac.blocksAt]
      refine List.map_congr_left fun i hi => bytesAt_frame G9 (fun r hr => ?_) (by decide)
      have hi' := List.mem_range.mp hi
      obtain hsub : Region.Sub ⟨D.setWidth 64 + BitVec.ofNat 64 (8 * i), 8⟩ ⟨D.setWidth 64, 8 * n⟩ :=
        VG.Offset.sub_base _ (by omega_arith)
      rcases List.mem_cons.mp hr with rfl | hr
      · exact L.ds.sub_left hsub
      · rw [List.mem_singleton.mp hr]; exact h.bD.symm.sub_left hsub
    rw [U.mem, out', eK, eC, eB]

/-! ## A run of `update` -/

open VG.Proof.CmacTripleDes.Stream.X86 (UArgs UPost FArgs FPost)

/-- The function's call does what a run of `update` in its frame does. -/
theorem run_wp {s : State} {W C D S : BitVec 32} {n : Nat} (h : UArgs s W C D S n) :
    WP isa run s (UPost s W C D S n) := by
  have hsp := h.esp
  obtain b8 : Region.Sub (below (s.gpr .esp) 8) (below (s.gpr .esp) 24) := below_sub (by decide) hsp
  refine WP.mono (chain_wp (W := W) (C := C) (D := D) (S := S) (n := n) ⟨h.eax, h.edx, h.ebx, h.esi, h.edi,
    by omega_arith, ⟨h.hn, h.wc, h.ws, h.dc, h.ds.sub_right (Region.sub_prefix (by decide)), h.cs, h.fW, h.fC, h.fD,
      h.fS⟩, h.bW.sub_left b8, h.bD.sub_left b8, h.bC.sub_left b8, h.bS.sub_left b8, h.reads, h.writes⟩)
    fun s' p => ⟨p.rd, p.wr, p.saved, p.frame.sub fun r hr => ?_, p.out⟩
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), b8⟩

/-! ## A run of `finalize` -/

open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_frame writeBytes_nil)
open VG.Proof.CmacTripleDes (padded_bytes8 macFull_split8 subkeys_tdes)
open VG.Proof.CmacTripleDes.X86 (byte_rt32 b80 scheduleAt_frame)

section
variable {s : State} {K St P S : BitVec 32} {L : Nat}

theorem fin_inK {u : State} (h : FArgs s K St P S L) (hr : u.rd = s.rd) (hw : u.wr = s.wr) {o k : Nat}
    (ho : o + k ≤ 400) : InRegions (u.rd ++ u.wr) (K.setWidth 64 + BitVec.ofNat 64 o) k := by
  rw [hr, hw]
  exact h.reads _ _ ⟨⟨K.setWidth 64, 400⟩, List.mem_cons_self, VG.Offset.contains_base _ ho (by omega_arith)⟩

theorem fin_inP {u : State} (h : FArgs s K St P S L) (hr : u.rd = s.rd) (hw : u.wr = s.wr) {o k : Nat}
    (ho : o + k ≤ L) : InRegions (u.rd ++ u.wr) (P.setWidth 64 + BitVec.ofNat 64 o) k := by
  have := h.len
  rw [hr, hw]
  exact h.reads _ _ ⟨⟨P.setWidth 64, L⟩, List.mem_cons_of_mem _ List.mem_cons_self,
    VG.Offset.contains_base _ ho (by omega_arith)⟩

theorem fin_inS {u : State} (h : FArgs s K St P S L) (hw : u.wr = s.wr) {o k : Nat} (ho : o + k ≤ 640) :
    InRegions u.wr (sa S o) k := by
  rw [hw]
  exact h.writes _ _ ⟨⟨S.setWidth 64, 640⟩, List.mem_cons_of_mem _ List.mem_cons_self,
    VG.Offset.contains_base _ ho (by omega_arith)⟩

/-- A state of `fin` before the run that chains the last block: the
registers it keeps as at its entry, and memory `m`. -/
structure FCtx (s : State) (P S : BitVec 32) (L : Nat) (m : Mem) (t : State) : Prop where
  ebx : t.gpr .ebx = P
  esi : t.gpr .esi = BitVec.ofNat 32 L
  edi : t.gpr sb = S
  ebp : t.gpr .ebp = s.gpr .ebp
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = m

namespace FCtx
variable {m : Mem} {t t' : State}

theorem upd (c : FCtx s P S L m t) {d : Reg} {v : BitVec 32} (x : Upd t t' d v)
    (hd : d = .eax ∨ d = .ecx ∨ d = .edx) : FCtx s P S L m t' := by
  obtain o : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r := fun r a b c' =>
    x.other r (by rcases hd with rfl | rfl | rfl <;> assumption)
  exact ⟨(o _ (by decide) (by decide) (by decide)).trans c.ebx, (o _ (by decide) (by decide) (by decide)).trans c.esi,
    (o _ (by decide) (by decide) (by decide)).trans c.edi, (o _ (by decide) (by decide) (by decide)).trans c.ebp,
    (o _ (by decide) (by decide) (by decide)).trans c.esp, x.rd.trans c.rd, x.wr.trans c.wr, x.mem.trans c.mem⟩

theorem mupd (c : FCtx s P S L m t) {m' : Mem} (x : Mupd t t' m') : FCtx s P S L m' t' :=
  ⟨by rw [x.gpr]; exact c.ebx, by rw [x.gpr]; exact c.esi, by rw [x.gpr]; exact c.edi, by rw [x.gpr]; exact c.ebp,
    by rw [x.gpr]; exact c.esp, x.rd.trans c.rd, x.wr.trans c.wr, x.mem⟩

theorem fupd (c : FCtx s P S L m t) (x : Fupd t t') : FCtx s P S L m t' :=
  ⟨by rw [x.gpr]; exact c.ebx, by rw [x.gpr]; exact c.esi, by rw [x.gpr]; exact c.edi, by rw [x.gpr]; exact c.ebp,
    by rw [x.gpr]; exact c.esp, x.rd.trans c.rd, x.wr.trans c.wr, x.mem.trans c.mem⟩

/-- The same state, with its memory by another name. -/
theorem cast (c : FCtx s P S L m t) {m' : Mem} (e : m = m') : FCtx s P S L m' t := e ▸ c

end FCtx

/-- What the branch on the number of last bytes leaves: `Mₙ` (§6.2 step 4)
in `eax:edx`, and of memory only the slot of `Mₙ` changed. -/
structure BP (s : State) (K P S : BitVec 32) (L : Nat) (m : Mem) (t : State) : Prop where
  ctx : FCtx s P S L t.mem t
  frame : Frame [⟨sa S 464, 8⟩] m t.mem
  blk : le8 (t.gpr .edx ++ t.gpr .eax) = Spec.Cmac.lastBlock 8 (bytesAt s.mem (K.setWidth 64 + BitVec.ofNat 64 384) 8)
    (bytesAt s.mem (K.setWidth 64 + BitVec.ofNat 64 392) 8) (bytesAt s.mem (P.setWidth 64) L)

/-- A whole last block: `Mₙ* ⊕ K1`. -/
theorem full_wp (h : FArgs s K St P S L) (hL : L = 8) {m : Mem} (fm : Frame [⟨sa S 472, 16⟩] s.mem m)
    (sK : m.readW (sa S 480) 32 = K) {t : State} (c : FCtx s P S L m t) :
    WP isa (.block full) t (BP s K P S L m) := by
  subst hL
  have fK := h.fK
  have fP := h.fP
  have fS := h.fS
  refine ld (a := P.setWidth 64 + BitVec.ofNat 64 0) c.ebx (a0 rfl (by omega_arith))
    (fin_inP h c.rd c.wr (by decide)) fun t₁ v₁ => ?_
  obtain c₁ := c.upd v₁ (by decide)
  refine ld (a := P.setWidth 64 + BitVec.ofNat 64 4) c₁.ebx (a0 rfl (by omega_arith))
    (fin_inP h c₁.rd c₁.wr (by decide)) fun t₂ v₂ => ?_
  obtain c₂ := c₁.upd v₂ (by decide)
  refine ld (a := sa S 480) c₂.edi (a0 rfl (by omega_arith)) (Rg.ofWr (fin_inS h c₂.wr (by decide))) fun t₃ v₃ => ?_
  obtain c₃ := c₂.upd v₃ (by decide)
  obtain ecx₃ : t₃.gpr .ecx = K := by rw [v₃.gpr, c₂.mem]; exact sK
  refine xm (a := K.setWidth 64 + BitVec.ofNat 64 384) ecx₃ (a0 rfl (by omega_arith))
    (fin_inK h c₃.rd c₃.wr (by decide)) fun t₄ v₄ => ?_
  obtain c₄ := c₃.upd v₄ (by decide)
  refine xm (a := K.setWidth 64 + BitVec.ofNat 64 388) ((v₄.other _ (by decide)).trans ecx₃)
    (a0 rfl (by omega_arith)) (fin_inK h c₄.rd c₄.wr (by decide)) fun t₅ v₅ => WP.block_nil ?_
  obtain c₅ := c₄.upd v₅ (by decide)
  obtain eax₅ : t₅.gpr .eax = m.readW (P.setWidth 64 + BitVec.ofNat 64 0) 32 ^^^
      m.readW (K.setWidth 64 + BitVec.ofNat 64 384) 32 := by
    rw [v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, c₃.mem, c.mem]
  obtain edx₅ : t₅.gpr .edx = m.readW (P.setWidth 64 + BitVec.ofNat 64 4) 32 ^^^
      m.readW (K.setWidth 64 + BitVec.ofNat 64 388) 32 := by
    rw [v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, c₄.mem, c₁.mem]
  refine ⟨c₅.cast c₅.mem.symm, by rw [c₅.mem]; exact Frame.refl _ _, ?_⟩
  rw [eax₅, edx₅, ← BitVec.xor_append, le8_xor, le8_pair m (BitVec.add_zero _) rfl,
    le8_pair m rfl (VG.Offset.add_add_eq (a := 384) (b := 4) (c := 388) _ rfl).symm,
    bytesAt_frame fm (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact h.ps.sub_right (VG.Offset.sub_base _ (by decide))) (by decide),
    bytesAt_frame fm (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (h.ks.sub_left (VG.Offset.sub_base _ (by decide))).sub_right (VG.Offset.sub_base _ (by decide)))
      (by decide)]
  simp only [Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, ite_true]
  exact Proof.Cmac.xor_comm _ _

/-- Byte `i` of the last bytes to `Mₙ`'s slot, if there are more than `i` of
them. -/
theorem copyByte_wp (h : FArgs s K St P S L) {m₆ : Mem} (f6 : Frame [⟨sa S 464, 24⟩] s.mem m₆) {i : Nat}
    (hi : i < 8) {t : State}
    (c : FCtx s P S L (writeBytes m₆ (sa S 464) (bytesAt s.mem (P.setWidth 64) (min i L))) t) :
    WP isa (copyByte i) t
      (FCtx s P S L (writeBytes m₆ (sa S 464) (bytesAt s.mem (P.setWidth 64) (min (i + 1) L)))) := by
  have hL := h.len
  have fP := h.fP
  have fS := h.fS
  show WP isa (.seq (.block ([.alu .cmp .esi (.imm (BitVec.ofNat 32 (i + 1)))] : List Instr))
    (.ite .b (.block []) (.block [.movzx8 .eax (at_ .ebx i), .store8 (at_ sb (oMn + i)) .al]))) t _
  refine WP.seq (wp_cmpi fun t₁ f₁ cf₁ _ => WP.block_nil ?_)
  obtain c₁ := c.fupd f₁
  obtain ev : isa.eval .b t₁ = some (decide (L < i + 1)) := by
    show t₁.cf = _
    rw [cf₁, c.esi, toNat_ofNat_lt (by omega_arith), toNat_ofNat_lt (by omega_arith)]
  by_cases hlt : L < i + 1
  · refine WP.ite true (by rw [ev]; simp [hlt]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact c₁.cast (by rw [show min (i + 1) L = min i L by omega_arith])
  refine WP.ite false (by rw [ev]; simp [hlt]) (fun h => by cases h) fun _ => ?_
  obtain e₀ : min i L = i := by omega_arith
  obtain e₁ : min (i + 1) L = i + 1 := by omega_arith
  refine lb (a := P.setWidth 64 + BitVec.ofNat 64 i) c₁.ebx (a0 rfl (by omega_arith))
    (fin_inP h c₁.rd c₁.wr (by omega_arith)) fun t₂ v₂ => ?_
  obtain c₂ := c₁.upd v₂ (by decide)
  refine sb8 (a := sa S 464 + BitVec.ofNat 64 i) c₂.edi
    ((a0 (c := 464 + i) rfl (by omega_arith)).trans (VG.Offset.add_add _ 464 i).symm)
    (by rw [VG.Offset.add_add]; exact fin_inS h c₂.wr (by omega_arith)) fun t₃ w₃ => WP.block_nil ?_
  refine (c₂.mupd w₃).cast ?_
  obtain fW : Frame [⟨sa S 464, 24⟩] s.mem t₁.mem := by
    rw [c₁.mem]
    exact f6.trans ((writeBytes_frame _ _ _ (by
      rw [Proof.Cmac.bytesAt_length, e₀]
      exact VG.Offset.contains _ (Nat.le_refl _) (by omega_arith) (by decide))))
  obtain eb : t₁.mem (P.setWidth 64 + BitVec.ofNat 64 i) = s.mem (P.setWidth 64 + BitVec.ofNat 64 i) :=
    fW.bytes (R := ⟨P.setWidth 64, L⟩) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact h.ps.sub_right (VG.Offset.sub_base _ (by decide))) (show L ≤ 2 ^ 64 by omega_arith)
      (show i < L by omega_arith)
  rw [show Reg8.al.reg = .eax from rfl, v₂.gpr, byte_rt32, eb, c₂.mem, e₀, e₁, Proof.Cmac.bytesAt_succ,
    writeBytes_snoc _ _ _ _ (by rw [Proof.Cmac.bytesAt_length]; omega_arith), Proof.Cmac.bytesAt_length]

/-- Fewer than eight last bytes: `K2 ⊕ (Mₙ* ‖ 10ʲ)`. -/
theorem partial_wp (h : FArgs s K St P S L) (hL : L < 8) {m : Mem} (fm : Frame [⟨sa S 472, 16⟩] s.mem m)
    (sK : m.readW (sa S 480) 32 = K) {t : State} (c : FCtx s P S L m t) :
    WP isa partialBlock t (BP s K P S L m) := by
  have fK := h.fK
  have fP := h.fP
  have fS := h.fS
  show WP isa (.seq (.block [.mov .eax (.imm 0), .store (at_ sb oMn) .eax, .store (at_ sb (oMn + 4)) .eax])
    (.seq (copyByte 0) (.seq (copyByte 1) (.seq (copyByte 2) (.seq (copyByte 3) (.seq (copyByte 4)
      (.seq (copyByte 5) (.seq (copyByte 6) (.block padK2)))))))) ) t _
  -- zeros in the slot
  refine WP.seq (wp_movi fun t₁ v₁ => ?_)
  obtain c₁ := c.upd v₁ (by decide)
  refine st (a := sa S 464) c₁.edi (a0 rfl (by omega_arith)) (fin_inS h c₁.wr (by decide)) fun t₂ w₂ => ?_
  obtain c₂ := c₁.mupd w₂
  refine st (a := sa S 468) c₂.edi (a0 rfl (by omega_arith)) (fin_inS h c₂.wr (by decide))
    fun t₃ w₃ => WP.block_nil ?_
  obtain e468 : sa S 468 = sa S 464 + BitVec.ofNat 64 4 := (VG.Offset.add_add_eq (a := 464) (b := 4) (c := 468) _ rfl).symm
  obtain c₃ : FCtx s P S L ((m.writeW (sa S 464) 0).writeW (sa S 468) 0) t₃ :=
    (c₂.mupd w₃).cast (by rw [w₂.mem, w₂.gpr, v₁.gpr, v₁.mem, c.mem])
  obtain f6' : Frame [⟨sa S 464, 8⟩] m ((m.writeW (sa S 464) (0 : BitVec 32)).writeW (sa S 468) (0 : BitVec 32)) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (VG.Offset.contains _ (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (VG.Offset.contains _ (by decide) (by decide) (by decide))
  obtain hz : bytesAt ((m.writeW (sa S 464) (0 : BitVec 32)).writeW (sa S 468) (0 : BitVec 32)) (sa S 464) 8 =
      Spec.Cmac.zeros 8 := by
    rw [pair_le8 _ rfl e468]; decide
  generalize (m.writeW (sa S 464) (0 : BitVec 32)).writeW (sa S 468) (0 : BitVec 32) = m₆ at c₃ f6' hz
  obtain f6 : Frame [⟨sa S 464, 24⟩] s.mem m₆ :=
    (fm.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      obtain rfl := List.mem_singleton.mp hr
      exact VG.Offset.sub _ (by decide) (by decide)⟩).trans
    (f6'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      obtain rfl := List.mem_singleton.mp hr
      exact VG.Offset.sub _ (by decide) (by decide)⟩)
  -- the bytes
  obtain c0 : FCtx s P S L (writeBytes m₆ (sa S 464) (bytesAt s.mem (P.setWidth 64) (min 0 L))) t₃ :=
    c₃.cast (by rw [Nat.zero_min, show bytesAt s.mem (P.setWidth 64) 0 = [] from rfl, writeBytes_nil])
  refine WP.seq (WP.mono (copyByte_wp h f6 (by decide) c0) fun _ c1 =>
    WP.seq (WP.mono (copyByte_wp h f6 (by decide) c1) fun _ c2 =>
    WP.seq (WP.mono (copyByte_wp h f6 (by decide) c2) fun _ c3 =>
    WP.seq (WP.mono (copyByte_wp h f6 (by decide) c3) fun _ c4 =>
    WP.seq (WP.mono (copyByte_wp h f6 (by decide) c4) fun _ c5 =>
    WP.seq (WP.mono (copyByte_wp h f6 (by decide) c5) fun _ c6 =>
    WP.seq (WP.mono (copyByte_wp h f6 (by decide) c6) fun u c7 => ?_)))))))
  obtain hlen : (bytesAt s.mem (P.setWidth 64) L).length = L := Proof.Cmac.bytesAt_length _ _ _
  obtain c7 : FCtx s P S L (writeBytes m₆ (sa S 464) (bytesAt s.mem (P.setWidth 64) L)) u :=
    c7.cast (by rw [show min (6 + 1) L = L by omega_arith])
  -- the padding, and `K2`
  refine wp_mov fun u₁ x₁ => ?_
  obtain d₁ := c7.upd x₁ (by decide)
  refine wp_add fun u₂ x₂ _ => ?_
  obtain d₂ := d₁.upd x₂ (by decide)
  refine wp_movi fun u₃ x₃ => ?_
  obtain d₃ := d₂.upd x₃ (by decide)
  obtain ecx₃ : u₃.gpr .ecx = S + BitVec.ofNat 32 L := by
    rw [x₃.other _ (by decide), x₂.gpr, x₁.gpr, x₁.other _ (by decide), c7.edi, c7.esi]
  refine sb8 (a := sa S 464 + BitVec.ofNat 64 L) ecx₃
    ((addr_add (a := L) (b := 464) (c := 464 + L) (by omega_arith) (by omega_arith)).trans (VG.Offset.add_add _ 464 L).symm)
    (by rw [VG.Offset.add_add]; exact fin_inS h d₃.wr (by omega_arith)) fun u₄ y₄ => ?_
  obtain d₄ := (d₃.mupd y₄).cast (m' := (writeBytes m₆ (sa S 464) (bytesAt s.mem (P.setWidth 64) L)).writeW
      (sa S 464 + BitVec.ofNat 64 (bytesAt s.mem (P.setWidth 64) L).length) (0x80 : Byte)) (by
    rw [show Reg8.al.reg = .eax from rfl, x₃.gpr, b80, d₃.mem, hlen])
  obtain pad := padded_bytes8 m₆ (sa S 464) (bytesAt s.mem (P.setWidth 64) L) (by rw [hlen]; exact hL) hz
  obtain fX : Frame [⟨sa S 464, 8⟩] m₆ ((writeBytes m₆ (sa S 464) (bytesAt s.mem (P.setWidth 64) L)).writeW
      (sa S 464 + BitVec.ofNat 64 (bytesAt s.mem (P.setWidth 64) L).length) (0x80 : Byte)) :=
    (writeBytes_frame _ _ _ (by
      rw [hlen]; exact VG.Offset.contains _ (Nat.le_refl _) (by omega_arith) (by decide))).writeW
      (List.mem_singleton_self _) _ (by rw [hlen]; exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith))
  generalize (writeBytes m₆ (sa S 464) (bytesAt s.mem (P.setWidth 64) L)).writeW
      (sa S 464 + BitVec.ofNat 64 (bytesAt s.mem (P.setWidth 64) L).length) (0x80 : Byte) = mX at d₄ pad fX
  obtain fmX : Frame [⟨sa S 464, 8⟩] m mX := f6'.trans fX
  obtain fsX : Frame [⟨sa S 464, 24⟩] s.mem mX := f6.trans (fX.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    obtain rfl := List.mem_singleton.mp hr
    exact VG.Offset.sub _ (by decide) (by decide)⟩)
  refine ld (a := sa S 464) d₄.edi (a0 rfl (by omega_arith)) (Rg.ofWr (fin_inS h d₄.wr (by decide))) fun u₅ x₅ => ?_
  obtain d₅ := d₄.upd x₅ (by decide)
  refine ld (a := sa S 468) d₅.edi (a0 rfl (by omega_arith)) (Rg.ofWr (fin_inS h d₅.wr (by decide))) fun u₆ x₆ => ?_
  obtain d₆ := d₅.upd x₆ (by decide)
  refine ld (a := sa S 480) d₆.edi (a0 rfl (by omega_arith)) (Rg.ofWr (fin_inS h d₆.wr (by decide))) fun u₇ x₇ => ?_
  obtain d₇ := d₆.upd x₇ (by decide)
  obtain ecx₇ : u₇.gpr .ecx = K := by
    rw [x₇.gpr, d₆.mem, slot_keep fmX (.inr (by decide)) (by decide) (by decide)]; exact sK
  refine xm (a := K.setWidth 64 + BitVec.ofNat 64 392) ecx₇ (a0 rfl (by omega_arith))
    (fin_inK h d₇.rd d₇.wr (by decide)) fun u₈ x₈ => ?_
  obtain d₈ := d₇.upd x₈ (by decide)
  refine xm (a := K.setWidth 64 + BitVec.ofNat 64 396) ((x₈.other _ (by decide)).trans ecx₇)
    (a0 rfl (by omega_arith)) (fin_inK h d₈.rd d₈.wr (by decide)) fun u₉ x₉ => WP.block_nil ?_
  obtain d₉ := d₈.upd x₉ (by decide)
  obtain eax₉ : u₉.gpr .eax = mX.readW (sa S 464) 32 ^^^ mX.readW (K.setWidth 64 + BitVec.ofNat 64 392) 32 := by
    rw [x₉.other _ (by decide), x₈.gpr, x₇.other _ (by decide), x₆.other _ (by decide), x₅.gpr, d₇.mem, d₄.mem]
  obtain edx₉ : u₉.gpr .edx = mX.readW (sa S 468) 32 ^^^ mX.readW (K.setWidth 64 + BitVec.ofNat 64 396) 32 := by
    rw [x₉.gpr, x₈.other _ (by decide), x₇.other _ (by decide), x₆.gpr, d₈.mem, d₅.mem]
  refine ⟨d₉.cast d₉.mem.symm, by rw [d₉.mem]; exact fmX, ?_⟩
  rw [hlen] at pad
  rw [eax₉, edx₉, ← BitVec.xor_append, le8_xor, le8_pair mX rfl e468,
    le8_pair mX rfl (VG.Offset.add_add_eq (a := 392) (b := 4) (c := 396) _ rfl).symm, pad,
    bytesAt_frame fsX (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (h.ks.sub_left (VG.Offset.sub_base _ (by decide))).sub_right (VG.Offset.sub_base _ (by decide)))
      (by decide)]
  simp only [Spec.Cmac.lastBlock, hlen, show L ≠ 8 by omega_arith, ite_false]
  exact Proof.Cmac.xor_comm _ _

end

end VG.Proof.CmacTripleDes.X86.Ssse3
