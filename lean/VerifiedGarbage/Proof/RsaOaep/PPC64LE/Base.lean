module

public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Target

/-! ### `RsaOaep.PPC64LE.Frame`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP encryption on PPC64LE: the frame

Untrusted: everything here is checked by Lean. The frame of
`vg_rsa_oaep_<H>_mgf1_encrypt_precomputed` (`Impl/RsaOaep/PPC64LE.lean`),
from its base `fb`, and the 48 bytes below it that the streaming hash
functions use (`cR`): the stack the function uses, `kR`, the 304 bytes below
the stack pointer on entry. As for RSASSA-PKCS1-v1_5
(`Proof/RsaPkcs1Sig/PPC64LE/Frame.lean`): `save_ok`, the saves of
`r14`–`r29` and of the return address; `Saves`, what the restores need, kept
by code writing other registers and memory apart from the slots;
`restore_ok`, the restores giving back the caller's registers.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_addSp wp_mflr wp_std wp_ld wp_mtlr)

/-! ## Addresses -/

/-- The frame's base: the stack pointer in the frame. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses: the frame and the 48 bytes below it. -/
abbrev kR (s : State) : Region := below s.sp 304

/-- The frame's local variable space, which its push makes writable. -/
abbrev fr (s : State) : Region := ⟨fb s + BitVec.ofNat 64 32, frameBytes - 32⟩

/-- The 48 bytes below the frame, which the streaming hash functions use. -/
abbrev cR (s : State) : Region := below (fb s) 48

theorem frameR_eq (s : State) : frameR frameBytes s = fr s := rfl

/-- An address of the frame, from the base of `kR`. -/
theorem fb_off (s : State) (d : Nat) :
    fb s + BitVec.ofNat 64 d = (s.sp - BitVec.ofNat 64 304) + BitVec.ofNat 64 (48 + d) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_comm, show (304 : Nat) = frameBytes + 48 from rfl]
  bv_omega

theorem cR_eq (s : State) : cR s = ⟨s.sp - BitVec.ofNat 64 304, 48⟩ := by
  simp only [cR, below, Region.mk.injEq, and_true]
  rw [BitVec.sub_sub]; rfl

/-- A region of the frame is in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (kR s) := by
  rw [fb_off]; exact Offset.sub_base _ (by unfold frameBytes at h; omega_using [h])

theorem frame_contains (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (kR s).Contains (fb s + BitVec.ofNat 64 d) n := by
  rw [fb_off]
  exact Offset.contains_base _ (by unfold frameBytes at h; omega_using [h]) (by unfold frameBytes at h; omega_using [h])

theorem cR_sub (s : State) : Region.Sub (cR s) (kR s) := by
  have := Offset.sub_base (s.sp - BitVec.ofNat 64 304) (d := 0) (n := 48) (k := 304) (by omega_using [])
  rw [BitVec.add_zero] at this; rw [cR_eq]; exact this

/-- The local variable space is writable. -/
theorem in_fr (s : State) (rs : List Region) {d n : Nat} (h₁ : 32 ≤ d) (h : d + n ≤ frameBytes) :
    InRegions (fr s :: rs) (fb s + BitVec.ofNat 64 d) n :=
  ⟨_, List.mem_cons_self .., Offset.contains _ h₁ (by unfold frameBytes at *; omega_using [h])
    (by unfold frameBytes; omega_using [])⟩

theorem in_fr' (s : State) (rd rs : List Region) {d n : Nat} (h₁ : 32 ≤ d) (h : d + n ≤ frameBytes) :
    InRegions (rd ++ fr s :: rs) (fb s + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := in_fr s rs h₁ h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- Our stack arguments, from the frame. -/
theorem stackArgAddr_fb (s : State) (j : Nat) :
    stackArgAddr s j = fb s + BitVec.ofNat 64 (arg j) := by
  have e : BitVec.ofNat 64 (arg j) = BitVec.ofNat 64 frameBytes + BitVec.ofNat 64 (32 + 8 * (8 + j)) := by
    rw [BitVec.ofNat_add_ofNat]; unfold arg; congr 1; omega_using []
  rw [stackArgAddr, e, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The call's stack arguments, in the frame. -/
theorem stackArgAddr_in (t : State) (j : Nat) :
    stackArgAddr t j = t.sp + BitVec.ofNat 64 (96 + 8 * j) := by
  rw [stackArgAddr, show 32 + 8 * (8 + j) = 96 + 8 * j by omega_using []]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.add_zero]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 32 + 8 * 8 + 8 * j = 32 + 8 * (8 + j) by omega_using []]

/-! ## The saves -/

/-- The callee-saved registers other than `r14`–`r29`. -/
def hiRegs : List Reg := [.r2, .r30, .r31]

theorem save_eq : save = ([.addSp .r12 0] : List Instr) ++ Spill.saveCode .r12 saved ++
    ([.mflr .r0, .store .d .r0 .r12 oLr] : List Instr) :=
  rfl

theorem restore_eq :
    restore = ([.addSp .r12 0, .load .d .r0 .r12 oLr, .mtlr .r0] : List Instr) ++ Spill.restoreCode .r12 saved :=
  rfl

theorem saved_offs : ∀ p ∈ saved, 112 ≤ p.2 ∧ p.2 + 8 ≤ oLr := by decide

theorem saved_ho : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

theorem preserved_split {r : Reg} (h : r ∈ preserved) : r ∈ saved.map Prod.fst ∨ r ∈ hiRegs := by
  revert r; decide

/-- The saves, from the state after the frame's push (`u`): `r12` holds
the frame's base, `r14`–`r29` and the return address are in their slots, and
memory is changed only in the frame. -/
theorem save_ok {s u : State} (hsp : u.sp = fb s) (hwr : u.wr = fr s :: s.wr)
    (hm : Frame [kR s] s.mem u.mem) (hg : ∀ r ∈ preserved, u.gpr r = s.gpr r) (hlr : u.lr = s.lr)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ v, Keep [.r12, .r0] u v → v.gpr .r12 = fb s → Frame [kR s] s.mem v.mem →
      Spill.Saved (fb s) s.gpr saved v.mem → v.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr →
      WP isa (.block rest) v Q) :
    WP isa (.block (save ++ rest)) u Q := by
  rw [save_eq]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_addSp fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  refine Spill.save_ok (b := .r12) (l := saved) (by decide) saved_ho (fun p hp => ?_) ?_
  · have := saved_offs p hp
    rw [e₁, o₁.wr, hwr]; exact in_fr s _ (by omega_using [this]) (by unfold oLr frameBytes at *; omega_using [this])
  generalize hu₂ : ({ u₁ with mem := Spill.saveMem u₁.mem (u₁.gpr .r12) u₁.gpr saved } : State) = u₂
  have g₂ : u₂.gpr = u₁.gpr := by rw [← hu₂]
  have m₂ : u₂.mem = Spill.saveMem u.mem (fb s) u₁.gpr saved := by rw [← hu₂, e₁, o₁.mem]
  have k₂ : Keep [.r12] u u₂ := by
    rw [← hu₂]; exact ⟨fun r hr => o₁.gpr r hr, o₁.rd, o₁.wr, o₁.sp, o₁.lr⟩
  refine wp_mflr fun u₃ o₃ e₃ => wp_std (a := fb s + BitVec.ofNat 64 oLr)
    (by rw [o₃.get .r12, g₂, e₁]) (by rw [o₃.wr, k₂.wr, hwr]; exact in_fr s _ (by decide) (by decide))
    fun u₄ m₄ => ?_
  have hsl : Frame [⟨fb s, frameBytes⟩] u.mem u₂.mem := by
    rw [m₂]
    exact Spill.saveMem_frame_base (fun p hp => by
      have := saved_offs p hp; unfold oLr frameBytes at *; omega_using [this]) (by decide) _ _ _
  have hfk : Region.Sub ⟨fb s, frameBytes⟩ (kR s) := by
    have := frame_sub s (d := 0) (n := frameBytes) (by omega_using []); rwa [BitVec.add_zero] at this
  have fr₂ : Frame [kR s] s.mem u₂.mem :=
    hm.trans (hsl.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, hfk⟩)
  have sv₂ : Spill.Saved (fb s) s.gpr saved u₂.mem := by
    rw [m₂]
    refine fun p hp => (Spill.saveMem_saved (by decide) _ _ _ p hp).trans ?_
    have h12 : p.1 ∉ [Reg.r12] := by revert p; decide
    rw [o₁.gpr _ h12, hg _ (by revert p; decide)]
  have hd : ∀ p ∈ saved, ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 oLr, 8⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 p.2, 8⟩ r := fun p hp r hr => by
    have := saved_offs p hp
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega_using [this])) (by unfold oLr at *; omega_using [this]) (by decide)
  have fw : Frame [⟨fb s + BitVec.ofNat 64 oLr, 8⟩] u₃.mem u₄.mem := by
    rw [m₄.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine k u₄ ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
  · have h0 : r ∉ [Reg.r0] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; exact fun h => hr (.inr h)
    have h12 : r ∉ [Reg.r12] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; exact fun h => hr (.inl h)
    rw [m₄.gpr, o₃.gpr r h0, k₂.gpr r h12]
  · rw [m₄.rd, o₃.rd, k₂.rd]
  · rw [m₄.wr, o₃.wr, k₂.wr]
  · rw [m₄.sp, o₃.sp, k₂.sp]
  · rw [m₄.lr, o₃.lr, k₂.lr]
  · rw [m₄.gpr, o₃.get .r12, g₂, e₁]
  · rw [m₄.mem, o₃.mem]
    exact fr₂.writeW (List.mem_singleton_self _) _ (frame_contains s (by decide))
  · have : Spill.Saved (fb s) s.gpr saved u₃.mem := by rw [o₃.mem]; exact sv₂
    exact this.frame fw hd
  · rw [m₄.mem, Mem.readW_writeW_self64, e₃, k₂.lr, hlr]

/-- What the restores need: the frame, our caller's registers and return
address in their slots, and the other callee-saved registers as on entry. -/
structure Saves (s t : State) : Prop where
  sp : t.sp = fb s
  wr : t.wr = fr s :: s.wr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  ls : t.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr

/-- The slots: the saves and the return address. -/
abbrev slR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 112, oLr + 8 - 112⟩

theorem slR_sub (s : State) : Region.Sub (slR s) (kR s) := frame_sub s (by decide)

/-- `Saves` is kept by code writing registers other than the callee-saved
ones, and memory apart from the slots. -/
theorem Saves.keep {s t w : State} {rs : List Reg} (h : Saves s t) (o : Keep rs t w) {R : List Region}
    (hm : Frame R t.mem w.mem) (hR : ∀ r ∈ R, (slR s).Disjoint r) (hrs : ∀ r ∈ rs, r ∉ hiRegs := by decide) :
    Saves s w where
  sp := o.sp.trans h.sp
  wr := o.wr.trans h.wr
  hi := fun r hr => (o.gpr _ fun h' => hrs r h' hr).trans (h.hi r hr)
  sv := h.sv.frame hm fun p hp r hr => (hR r hr).sub_left (by
    have := saved_offs p hp
    exact Offset.sub _ (n := 8) (by omega_using [this]) (by unfold oLr at *; omega_using [this]))
  ls := by
    rw [hm.readW (Region.contains_self _ _) (fun r hr => (hR r hr).sub_left
      (Offset.sub _ (n := 8) (by decide) (by decide))) (by decide)]
    exact h.ls

/-- The restores: the caller's registers and return address are back, and
`r3` and memory are kept. -/
theorem restore_ok {s w : State} (hm : Saves s w) :
    WP isa (.block restore) w fun w' =>
      abiPreserved s (freed frameBytes w') ∧ w'.gpr .r3 = w.gpr .r3 ∧ w'.mem = w.mem := by
  rw [restore_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun w₁ o₁ e₁ => ?_
  rw [hm.sp, BitVec.add_zero] at e₁
  have hin : ∀ {e : Nat}, 112 ≤ e → e + 8 ≤ oLr + 8 →
      InRegions (w₁.rd ++ w₁.wr) (fb s + BitVec.ofNat 64 e) 8 := fun h₁ h₂ => by
    rw [o₁.wr, hm.wr]; exact in_fr' s _ _ (by omega_using [h₁]) (by unfold oLr frameBytes at *; omega_using [h₂])
  refine wp_ld (a := fb s + BitVec.ofNat 64 oLr) (by rw [e₁]) (hin (by decide) (by decide)) fun w₂ o₂ e₂ =>
    wp_mtlr fun w₃ g₃ m₃ rd₃ wr₃ sp₃ lr₃ => ?_
  refine WP.mono (Spill.restore_wp (b := .r12) (l := saved) (B := fb s) (g := s.gpr) (by decide)
    (by rw [g₃, o₂.get .r12, e₁]) saved_ho (by decide)
    (fun p hp => by
      have := saved_offs p hp
      rw [rd₃, wr₃, o₂.rd, o₂.wr]; exact hin this.1 (by omega_using [this]))
    (by rw [m₃, o₂.mem, o₁.mem]; exact hm.sv)) fun w' hr => ⟨⟨fun r hr' => ?_, ?_, ?_⟩, ?_, ?_⟩
  · show w'.gpr r = s.gpr r
    rcases preserved_split hr' with h | h
    · exact hr.gpr_of (.inl h)
    · have h0 : r ∉ saved.map Prod.fst := by revert r; decide
      have h1 : r ∉ [Reg.r0] := by revert r; decide
      have h2 : r ∉ [Reg.r12] := by revert r; decide
      rw [hr.other r h0, g₃, o₂.gpr r h1, o₁.gpr r h2]; exact hm.hi r h
  · show w'.sp + BitVec.ofNat 64 frameBytes = s.sp
    rw [hr.sp, sp₃, o₂.sp, o₁.sp, hm.sp, BitVec.sub_add_cancel]
  · have h₁ := hr.lr
    have h₂ : w₁.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr := by rw [o₁.mem]; exact hm.ls
    exact h₁.trans (lr₃.trans (e₂.trans h₂))
  · show w'.gpr .r3 = w.gpr .r3
    rw [hr.other .r3 (by decide), g₃, o₂.get .r3, o₁.get .r3]
  · rw [hr.mem, m₃, o₂.mem, o₁.mem]

end VG.Proof.RsaOaep.PPC64LE

end

end

/-!
# RSA paddings on PPC64LE: the state in the frame

Untrusted: everything here is checked by Lean. The code shared by the
functions that run in the frame of `Impl/RsaOaep/PPC64LE.lean` (RSAES-OAEP
encryption, RSASSA-PSS verification), for any entry state `s` whose working
space starts at `S s` and whose values of `r15`–`r23` are `vf s` (each
function's own). Our part of the working space, `SC S s` (its first `oRsa`
bytes), seen as a function from offsets to bytes (`view`); and
`Base S vf s t`: the state `t` is in the frame with our caller's registers and
return address in their slots (`Saves`), `r14` holds `S s` and `r15`–`r23`
their values, and memory is changed only in the stack the function uses and
in `SC S s`. Code that writes other registers, ranges of `SC S s` and the 48
bytes below the frame keeps it (`Base.keep`, `Base.only`), given what the
code needs of the entry state (`Fits`); the caller's buffers are then as on
entry (`bytes_entry`, `words_entry`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo)

/-- `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- Our part of the working space at `S s`. -/
abbrev SC (S : State → Addr) (s : State) : Region := ⟨S s, oRsa⟩

/-- Memory at `S`, as a function from offsets to bytes. -/
def view (m : Mem) (S : Addr) (o : Nat) : Byte := m (off S o)

/-- What the shared code needs of the entry state `s`, whose working space is
at `S s`: room for the frame and the calls below it, our part of the working
space writable and apart from that stack, and not wrapping around. -/
structure Fits (S : State → Addr) (s : State) : Prop where
  sp1 : 304 ≤ s.sp.toNat
  sc : ∃ R ∈ s.wr, R.base = S s ∧ oRsa ≤ R.len
  ksc : (kR s).Disjoint (SC S s)
  wS : (S s).toNat + oRsa ≤ 2 ^ 64

section
variable {S : State → Addr} {s : State} (P : Fits S s)
include P

omit P in
/-- A range of our part of the working space is in it. -/
theorem sc_in {o n : Nat} (h : o + n ≤ oRsa) : Region.Sub ⟨off (S s) o, n⟩ (SC S s) :=
  Offset.sub_base _ h

/-- A range of our part of the working space is writable. -/
theorem sc_cov {o n : Nat} (h : o + n ≤ oRsa) : Covers [⟨off (S s) o, n⟩] (fr s :: s.wr) :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    obtain ⟨R, hR, hb, hl⟩ := P.sc
    exact ⟨R, List.mem_cons_of_mem _ hR, o, by rw [hb], by simp only; omega_using [h, hl]⟩

theorem sc_inR {o n : Nat} (h : o + n ≤ oRsa) (rd : List Region) :
    InRegions (rd ++ (fr s :: s.wr)) (off (S s) o) n :=
  Covers.right (sc_cov P h) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem sc_inW {o n : Nat} (h : o + n ≤ oRsa) : InRegions (fr s :: s.wr) (off (S s) o) n :=
  sc_cov P h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- Our part of the working space and the stack the function uses are apart. -/
theorem slR_sc : (slR s).Disjoint (SC S s) := P.ksc.sub_left (slR_sub s)

theorem cR_sc : (cR s).Disjoint (SC S s) := P.ksc.sub_left (cR_sub s)

omit P in
/-- Two ranges of our part of the working space that do not overlap. -/
theorem sdis {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ oRsa) (hb : b + k ≤ oRsa) :
    Region.Disjoint ⟨off (S s) a, n⟩ ⟨off (S s) b, k⟩ :=
  Offset.disjoint _ h (by unfold oRsa at ha; omega_using [ha]) (by unfold oRsa at hb; omega_using [hb])

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
    (.inl (by omega_using [])) (by omega_using []) (by decide)
  rwa [BitVec.add_zero] at this

/-! ## The state in the frame -/

/-- The registers `Base` fixes but `r14`. -/
def fx : List Reg := [.r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23]

structure Base (S : State → Addr) (vf : State → Reg → BitVec 64) (s t : State) : Prop where
  sv : Saves s t
  rd : t.rd = s.rd
  r14 : t.gpr .r14 = S s
  vs : ∀ r ∈ fx, t.gpr r = vf s r
  mem : Frame [kR s, SC S s] s.mem t.mem

/-- A region written by code that keeps `Base`: in our part of the working
space, or the 48 bytes below the frame. -/
def Ours (S : State → Addr) (s : State) (r : Region) : Prop := Region.Sub r (SC S s) ∨ r = cR s

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s t w : State} {rs : List Reg}

theorem Base.sp (h : Base S vf s t) : t.sp = fb s := h.sv.sp
theorem Base.wr (h : Base S vf s t) : t.wr = fr s :: s.wr := h.sv.wr

/-- `Base` is kept by code that keeps the stack pointer, the regions and the
registers it fixes, and writes memory only in our ranges. -/
theorem Base.of (P : Fits S s) (h : Base S vf s t) (hsp : w.sp = t.sp) (hrd : w.rd = t.rd) (hwr : w.wr = t.wr)
    (hg : ∀ r ∈ .r14 :: fx ++ hiRegs, w.gpr r = t.gpr r) {R : List Region} (hm : Frame R t.mem w.mem)
    (hR : ∀ r ∈ R, Ours S s r) : Base S vf s w where
  sv := by
    have hd : ∀ r ∈ R, (slR s).Disjoint r := fun r hr => by
      rcases hR r hr with h' | rfl
      · exact (slR_sc P).sub_right h'
      · exact (cR_slR s).symm
    refine ⟨hsp.trans h.sv.sp, hwr.trans h.sv.wr, fun r hr => (hg r (List.mem_append_right _ hr)).trans
      (h.sv.hi r hr), h.sv.sv.frame hm fun p hp r hr => (hd r hr).sub_left ?_, ?_⟩
    · have := saved_offs p hp
      exact Offset.sub _ (n := 8) (by omega_using [this]) (by unfold oLr at *; omega_using [this])
    · rw [hm.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left
        (Offset.sub _ (n := 8) (by decide) (by decide))) (by decide)]
      exact h.sv.ls
  rd := hrd.trans h.rd
  r14 := (hg _ (by decide)).trans h.r14
  vs := fun r hr => (hg r (List.mem_append_left _ (List.mem_cons_of_mem _ hr))).trans (h.vs r hr)
  mem := h.mem.trans (hm.sub fun r hr => by
    rcases hR r hr with h' | rfl
    · exact ⟨SC S s, by simp, h'⟩
    · exact ⟨kR s, by simp, cR_sub s⟩)

/-- `Base` is kept by code writing registers other than those it fixes and
the callee-saved ones it does not save, and memory in our ranges. -/
theorem Base.keep (P : Fits S s) (h : Base S vf s t) (o : Keep rs t w) {R : List Region}
    (hm : Frame R t.mem w.mem) (hR : ∀ r ∈ R, Ours S s r) (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) :
    Base S vf s w :=
  h.of P o.sp o.rd o.wr (fun r hr => o.gpr r fun h' => hrs r h' hr) hm hR

/-- `Base` is kept by code writing registers other than those it fixes and
the callee-saved ones it does not save. -/
theorem Base.only (P : Fits S s) (h : Base S vf s t) (o : Only rs t w)
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : Base S vf s w :=
  h.keep P o.keep (R := []) (by rw [o.mem]; exact Frame.refl _ _) (by simp) hrs

/-- A call keeps `Base` if it writes only our ranges and the 48 bytes below
the stack pointer, and keeps the callee-saved registers. -/
theorem Base.call (P : Fits S s) (h : Base S vf s t) {R : List Region} (hR : ∀ r ∈ R, Region.Sub r (SC S s))
    (hrd : w.rd = t.rd) (hwr : w.wr = t.wr) (hsp : w.sp = t.sp) (hm : Frame (R ++ [below t.sp 48]) t.mem w.mem)
    (hg : ∀ r ∈ preserved, w.gpr r = t.gpr r) : Base S vf s w :=
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
    exact Offset.contains_base _ (by omega_using [this]) (by omega_using [hl, this])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ha.symm
    · exact hb.symm

end VG.Proof.RsaOaep.PPC64LE
