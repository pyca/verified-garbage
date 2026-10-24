module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Pre
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP encryption on PPC64LE: the state in the frame

Untrusted: everything here is checked by Lean. From the entry state `s`:
our part of the working space, `SC s` (its first `oRsa` bytes, from `S s`),
seen as a function from offsets to bytes (`view`); and `Base s t`: the state
`t` is in the frame with our caller's registers and return address in their
slots (`Saves`), `r14`–`r23` hold the values they keep, and memory is
changed only in the stack the function uses and in `SC s`. Code that writes
other registers, ranges of `SC s` and the 48 bytes below the frame keeps it
(`Base.keep`, `Base.only`); the caller's buffers are then as on entry
(`bytes_entry`, `words_entry`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo)

/-- `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- The working space. -/
abbrev S (s : State) : Addr := stackArg s 3

/-- Our part of it. -/
abbrev SC (s : State) : Region := ⟨S s, oRsa⟩

/-- Memory at `S`, as a function from offsets to bytes. -/
def view (m : Mem) (S : Addr) (o : Nat) : Byte := m (off S o)

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

theorem scLen : oRsa ≤ (stackArg s 4).toNat * 8 := by
  have := P.hs; unfold Spec.RsaPss.publicScratchWords at this; unfold oRsa; omega

theorem sc_sub : Region.Sub (SC s) (scR s) := Region.sub_prefix (scLen P)

omit P in
/-- A range of our part of the working space is in it. -/
theorem sc_in {o n : Nat} (h : o + n ≤ oRsa) : Region.Sub ⟨off (S s) o, n⟩ (SC s) :=
  Offset.sub_base _ h

theorem scR_contains {o n : Nat} (h : o + n ≤ oRsa) : (scR s).Contains (off (S s) o) n :=
  Offset.contains_base _ (by have := scLen P; omega) (by unfold oRsa at h; omega)

/-- A range of our part of the working space is writable. -/
theorem sc_cov {o n : Nat} (h : o + n ≤ oRsa) : Covers [⟨off (S s) o, n⟩] (fr s :: s.wr) :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨scR s, by rw [P.hwr]; simp, o, rfl, by have := scLen P; simp only; omega⟩

theorem sc_inR {o n : Nat} (h : o + n ≤ oRsa) (rd : List Region) :
    InRegions (rd ++ (fr s :: s.wr)) (off (S s) o) n :=
  Covers.right (sc_cov P h) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem sc_inW {o n : Nat} (h : o + n ≤ oRsa) : InRegions (fr s :: s.wr) (off (S s) o) n :=
  sc_cov P h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- Our part of the working space and the stack the function uses are apart. -/
theorem k_sc : (kR s).Disjoint (SC s) := P.ksc.sub_right (sc_sub P)

theorem slR_sc : (slR s).Disjoint (SC s) := (k_sc P).sub_left (slR_sub s)

theorem cR_sc : (cR s).Disjoint (SC s) := (k_sc P).sub_left (cR_sub s)

omit P in
/-- Two ranges of our part of the working space that do not overlap. -/
theorem sdis {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ oRsa) (hb : b + k ≤ oRsa) :
    Region.Disjoint ⟨off (S s) a, n⟩ ⟨off (S s) b, k⟩ :=
  Offset.disjoint _ h (by unfold oRsa at ha; omega) (by unfold oRsa at hb; omega)

/-- The 48 bytes below the frame and a range of our part of the working space. -/
theorem cR_dis {o n : Nat} (h : o + n ≤ oRsa) : (cR s).Disjoint ⟨off (S s) o, n⟩ :=
  (cR_sc P).sub_right (sc_in h)

end

theorem cR_slR (s : State) : (cR s).Disjoint (slR s) := by
  rw [cR_eq]
  have e : slR s = ⟨(s.sp - BitVec.ofNat 64 304) + BitVec.ofNat 64 (48 + 112), oLr + 8 - 112⟩ := by
    simp only [slR]; rw [fb_off]
  rw [e]
  have := Offset.disjoint (s.sp - BitVec.ofNat 64 304) (d := 0) (n := 48) (e := 48 + 112) (k := oLr + 8 - 112)
    (.inl (by omega)) (by omega) (by decide)
  rwa [BitVec.add_zero] at this

/-! ## The state in the frame -/

/-- The registers `Base` fixes. -/
def fx : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23]

structure Base (s t : State) : Prop where
  sv : Saves s t
  rd : t.rd = s.rd
  r14 : t.gpr .r14 = stackArg s 3
  r15 : t.gpr .r15 = s.gpr .r6
  r16 : t.gpr .r16 = s.gpr .r3
  r17 : t.gpr .r17 = s.gpr .r7
  r18 : t.gpr .r18 = s.gpr .r8
  r19 : t.gpr .r19 = s.gpr .r9
  r20 : t.gpr .r20 = s.gpr .r10
  r21 : t.gpr .r21 = stackArg s 5
  r22 : t.gpr .r22 = stackArg s 6
  r23 : t.gpr .r23 = stackArg s 4
  mem : Frame [kR s, SC s] s.mem t.mem

/-- A region written by code that keeps `Base`: in our part of the working
space, or the 48 bytes below the frame. -/
def Ours (s : State) (r : Region) : Prop := Region.Sub r (SC s) ∨ r = cR s

section
variable {D : Nat} {s t w : State} {rs : List Reg}

theorem Base.sp (h : Base s t) : t.sp = fb s := h.sv.sp
theorem Base.wr (h : Base s t) : t.wr = fr s :: s.wr := h.sv.wr

theorem not_fx {r : Reg} (hrs : ∀ r ∈ rs, r ∉ fx ++ hiRegs) (hr : r ∈ fx) : r ∉ rs :=
  fun h' => hrs r h' (List.mem_append_left _ hr)

/-- `Base` is kept by code that keeps the stack pointer, the regions and the
registers it fixes, and writes memory only in our ranges. -/
theorem Base.of (P : PreO D s) (h : Base s t) (hsp : w.sp = t.sp) (hrd : w.rd = t.rd) (hwr : w.wr = t.wr)
    (hg : ∀ r ∈ fx ++ hiRegs, w.gpr r = t.gpr r) {R : List Region} (hm : Frame R t.mem w.mem)
    (hR : ∀ r ∈ R, Ours s r) : Base s w where
  sv := by
    have hd : ∀ r ∈ R, (slR s).Disjoint r := fun r hr => by
      rcases hR r hr with h' | rfl
      · exact (slR_sc P).sub_right h'
      · exact (cR_slR s).symm
    refine ⟨hsp.trans h.sv.sp, hwr.trans h.sv.wr, fun r hr => (hg r (List.mem_append_right _ hr)).trans
      (h.sv.hi r hr), h.sv.sv.frame hm fun p hp r hr => (hd r hr).sub_left ?_, ?_⟩
    · have := saved_offs p hp
      exact Offset.sub _ (n := 8) (by omega) (by unfold oLr at *; omega)
    · rw [hm.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left
        (Offset.sub _ (n := 8) (by decide) (by decide))) (by decide)]
      exact h.sv.ls
  rd := hrd.trans h.rd
  r14 := (hg _ (by decide)).trans h.r14
  r15 := (hg _ (by decide)).trans h.r15
  r16 := (hg _ (by decide)).trans h.r16
  r17 := (hg _ (by decide)).trans h.r17
  r18 := (hg _ (by decide)).trans h.r18
  r19 := (hg _ (by decide)).trans h.r19
  r20 := (hg _ (by decide)).trans h.r20
  r21 := (hg _ (by decide)).trans h.r21
  r22 := (hg _ (by decide)).trans h.r22
  r23 := (hg _ (by decide)).trans h.r23
  mem := h.mem.trans (hm.sub fun r hr => by
    rcases hR r hr with h' | rfl
    · exact ⟨SC s, by simp, h'⟩
    · exact ⟨kR s, by simp, cR_sub s⟩)

/-- `Base` is kept by code writing registers other than those it fixes and
the callee-saved ones it does not save, and memory in our ranges. -/
theorem Base.keep (P : PreO D s) (h : Base s t) (o : Keep rs t w) {R : List Region} (hm : Frame R t.mem w.mem)
    (hR : ∀ r ∈ R, Ours s r) (hrs : ∀ r ∈ rs, r ∉ fx ++ hiRegs := by decide) : Base s w :=
  h.of P o.sp o.rd o.wr (fun r hr => o.gpr r fun h' => hrs r h' hr) hm hR

/-- `Base` is kept by code writing registers other than those it fixes and
the callee-saved ones it does not save. -/
theorem Base.only (P : PreO D s) (h : Base s t) (o : Only rs t w) (hrs : ∀ r ∈ rs, r ∉ fx ++ hiRegs := by decide) :
    Base s w :=
  h.keep P o.keep (R := []) (by rw [o.mem]; exact Frame.refl _ _) (by simp) hrs

/-- A call keeps `Base` if it writes only our ranges and the 48 bytes below
the stack pointer, and keeps the callee-saved registers. -/
theorem Base.call (P : PreO D s) (h : Base s t) {R : List Region} (hR : ∀ r ∈ R, Region.Sub r (SC s))
    (hrd : w.rd = t.rd) (hwr : w.wr = t.wr) (hsp : w.sp = t.sp) (hm : Frame (R ++ [below t.sp 48]) t.mem w.mem)
    (hg : ∀ r ∈ preserved, w.gpr r = t.gpr r) : Base s w :=
  h.of P hsp hrd hwr (fun r hr => hg r (by revert r; decide)) hm fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact .inl (hR r hr)
    · rw [List.mem_singleton.mp hr, h.sp]; exact .inr rfl

end

/-! ## The caller's buffers -/

/-- A buffer that the function does not write. -/
theorem bytes_entry {A B : Region} {m m' : Mem} (hf : Frame [A, B] m m') {p : Addr} {len : Nat}
    (ha : A.Disjoint ⟨p, len⟩) (hb : B.Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p len = Spec.Rsa.bytesAt m p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ha.symm
  · exact hb.symm

theorem words_entry {A B : Region} {m m' : Mem} (hf : Frame [A, B] m m') {p : Addr} {n : Nat}
    (ha : A.Disjoint ⟨p, n * 8⟩) (hb : B.Disjoint ⟨p, n * 8⟩) (hl : p.toNat + n * 8 ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => hf.readW (r := ⟨p, n * 8⟩) ?_ (fun r hr => ?_) (by decide)
  · have := List.mem_range.mp hi
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ha.symm
    · exact hb.symm

end VG.Proof.RsaOaep.PPC64LE
