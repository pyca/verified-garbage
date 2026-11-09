module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Pre
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPre
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCall
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256Family
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Calls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.InitMain
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Finalize
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Common

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: from the frame to the calls after the private-key operation

Untrusted: everything here is checked by Lean. After the private-key
operation, every call is of SHA-256's streaming functions or of HMAC-SHA-256's
`init` and `finalize`, on states, keys and digests in `scratch`: each keeps
`Post` (`Post.after`), and gives what its contract says (`shaInit_ok`,
`shaUpd_ok`, `shaFin_ok`, `macInit_ok`, `macFin_ok`), with the memory it
changed (`After`).
-/

@[expose] public section

/-! ## `vg_rsa_pkcs1_decrypt` on RISC-V: `D = I2OSP(d, k)`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecD.lean`): from the call on, `Post s R EM`
holds: `Mid` with `out` and `scratch` written, `R` (the private-key
operation's result, zero-extended) in `s7` and `EM` in `out`.
`dBuild_ok`: `k` zeros at `scratch + sD`, then `d` at their end, which is
`I2OSP(OS2IP(d), k)` (`DB`).
-/

/-! ## `vg_rsa_pkcs1_decrypt` on RISC-V: the setup and the private-key operation

Untrusted: everything here is checked by Lean. As for signing
(`Proof/RsaPkcs1Sig/RISCV64/Sign/Call.lean`): the saves, the values kept in
`s0`–`s6`, the call's twelve stack arguments copied from ours and its
arguments in registers (`setup_ok`, into `AtCall`); the regions the call is
narrowed to (`callRd`, `callWr`) and its precondition (`preP_entry`); and
what it writes (`call_ok`, into `AtRet`).
-/

/-! ## `vg_rsa_pkcs1_decrypt` on RISC-V: the frame

Untrusted: everything here is checked by Lean. As for signing
(`Proof/RsaPkcs1Sig/RISCV64/Sign/Frame.lean`): the stack the function uses,
`kR`, is `vg_rsa_private_checked`'s frame (from `kb`) and then ours (`frR`,
from `fb`), which the allocation makes writable; the calls of SHA-256's and
HMAC's functions use less of it. `save_ok`: the saves of `s0`–`s9` and of the
return address `ra`. `Mid`: in the frame, the saved values in their slots,
`scratch`, `k`, `out`, `msg_len`, `d`, `d_len` and the input in `s0`–`s6`,
`s10` and `s11` as on entry, memory changed only in the stack and in the
regions `S`; it is kept by code writing other registers and the frame apart
from the slots (`Mid.keep`, `Mid.frameMem`). `restore_ok`: the restores give
back the caller's registers.
-/

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64

/-! ## Addresses -/

/-- The base of the stack the function and its callee use. -/
abbrev kb (s : State) : Addr := s.sp - BitVec.ofNat 64 stackBytes

/-- Our frame, which the allocation makes writable. -/
abbrev frR (s : State) : Region := ⟨fb s, frameBytes⟩

theorem fb_eq (s : State) : fb s = kb s + BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes := by
  apply BitVec.eq_of_toNat_eq
  simp only [fb, kb, stackBytes, frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes, BitVec.toNat_sub,
    BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem fb_off (s : State) (d : Nat) :
    fb s + BitVec.ofNat 64 d = kb s + BitVec.ofNat 64 (Impl.Rsa.RISCV64.Priv.frameBytes + d) := by
  rw [fb_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem fb_toNat {s : State} (h : DPre s) : (fb s).toNat + frameBytes = s.sp.toNat := by
  have := h.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stackBytes frameBytes at *
  unfold Impl.Rsa.RISCV64.Priv.frameBytes at *; omega

theorem kb_toNat {s : State} (h : DPre s) : (kb s).toNat + stackBytes = s.sp.toNat := by
  have := h.sp1
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stackBytes frameBytes at *
  unfold Impl.Rsa.RISCV64.Priv.frameBytes at *; omega

theorem fb_al {s : State} (h : DPre s) : (fb s).toNat % 16 = 0 := by
  have := fb_toNat h; have := h.sp16; unfold frameBytes at *; omega

theorem fb_al8 {s : State} (h : DPre s) {d : Nat} (hd : d % 8 = 0) : (fb s + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  Spill.al8 (by have := fb_al h; omega) hd

/-- A region of our frame is in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (kR s) := by
  rw [fb_off]
  exact Offset.sub_base _ (by unfold stackBytes frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at *; omega)

theorem frR_sub (s : State) : Region.Sub (frR s) (kR s) := by
  have := frame_sub s (d := 0) (n := frameBytes) (Nat.le_refl _)
  rwa [BitVec.add_zero] at this

/-- The callee's frame is in the stack the function uses. -/
theorem callee_sub (s : State) :
    Region.Sub ⟨fb s - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes,
      Impl.Rsa.RISCV64.Priv.frameBytes⟩ (kR s) := by
  rw [fb_eq, BitVec.add_sub_cancel]
  have := Offset.sub_base (kb s) (d := 0) (n := Impl.Rsa.RISCV64.Priv.frameBytes) (k := stackBytes)
    (by unfold stackBytes; omega)
  rwa [BitVec.add_zero] at this

/-- Our frame is writable. -/
theorem in_fr (s : State) (rs : List Region) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (frR s :: rs) (fb s + BitVec.ofNat 64 d) n :=
  ⟨_, List.mem_cons_self .., Offset.contains_base _ h (by unfold frameBytes at h; omega)⟩

theorem in_fr' (s : State) (rd rs : List Region) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (rd ++ frR s :: rs) (fb s + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := in_fr s rs h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- Our stack arguments, from the frame. -/
theorem stackArgAddr_fb (s : State) (j : Nat) :
    stackArgAddr s j = fb s + BitVec.ofNat 64 (frameBytes + 8 * j) := by
  rw [stackArgAddr, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem in_aR {s : State} {j : Nat} (hj : j < 15) : (aR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

/-! ## The saves -/

/-- The first byte of the slots, and the end of the last. -/
abbrev oSave : Nat := 96
abbrev oEnd : Nat := 184

/-- The callee-saved registers other than `s0`–`s9`. -/
def hiRegs : List Reg := [.s10, .s11]

/-- The registers `Mid` keeps. -/
def kept : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6] ++ hiRegs

/-- The saves of `s0`–`s9` and `ra`. -/
abbrev spill : List Instr := ([.addSp .t0 0] : List Instr) ++ Spill.saveCode .t0 saved

theorem save_eq : save = spill := rfl

theorem restore_eq : restore = ([.addSp .t0 0] : List Instr) ++ Spill.restoreCode .t0 saved := rfl

theorem saved_offs : ∀ p ∈ saved, oSave ≤ p.2 ∧ p.2 + 8 ≤ oEnd := by decide

theorem saved_ho : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem preserved_split {r : Reg} (h : r ∈ preserved) : r ∈ saved.map Prod.fst ∨ r ∈ hiRegs := by
  revert r; decide

/-- In the frame, from the entry state `s`: our caller's registers and
return address in their slots, `scratch`, `k`, `out`, `msg_len`, `d`, `d_len`
and the input in `s0`–`s6`, `s10` and `s11` as on entry, memory changed only
in the stack the function uses and the regions `S`. -/
structure Mid (S : List Region) (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = frR s :: s.wr
  s0 : t.gpr .s0 = stackArg s 13
  s1 : t.gpr .s1 = s.gpr .a4
  s2 : t.gpr .s2 = s.gpr .a0
  s3 : t.gpr .s3 = s.gpr .a2
  s4 : t.gpr .s4 = s.gpr .a7
  s5 : t.gpr .s5 = stackArg s 0
  s6 : t.gpr .s6 = stackArg s 1
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  mem : Frame (kR s :: S) s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem

section
variable {S : List Region} {s t w : State} {rs : List Reg}

theorem not_kept {r : Reg} (hrs : ∀ r ∈ rs, r ∉ kept) (hr : r ∈ kept) : r ∉ rs := fun h => hrs r h hr

theorem Mid.of {S' : List Region} (h : Mid S s t) (hg : ∀ r ∈ kept, w.gpr r = t.gpr r)
    (hsp : w.sp = t.sp) (hrd : w.rd = t.rd) (hwr : w.wr = t.wr) (hm : Frame (kR s :: S') s.mem w.mem)
    (hsv : Spill.Saved (fb s) s.gpr saved w.mem) : Mid S' s w where
  sp := hsp.trans h.sp
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  s0 := (hg _ (by decide)).trans h.s0
  s1 := (hg _ (by decide)).trans h.s1
  s2 := (hg _ (by decide)).trans h.s2
  s3 := (hg _ (by decide)).trans h.s3
  s4 := (hg _ (by decide)).trans h.s4
  s5 := (hg _ (by decide)).trans h.s5
  s6 := (hg _ (by decide)).trans h.s6
  hi := fun r hr => (hg _ (List.mem_append_right _ hr)).trans (h.hi r hr)
  mem := hm
  sv := hsv

/-- `Mid` is kept by code writing registers other than those it keeps, and
memory `hm` says is kept. -/
theorem Mid.keep {S' : List Region} (h : Mid S s t) (o : Kept rs t w)
    (hm : Frame (kR s :: S') s.mem w.mem) (hsv : Spill.Saved (fb s) s.gpr saved w.mem)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) : Mid S' s w :=
  h.of (fun r hr => o.gpr r (not_kept hrs hr)) o.sp o.rd o.wr hm hsv

/-- `Mid` is kept by code writing registers other than those it keeps. -/
theorem Mid.only (h : Mid S s t) (o : Only rs t w) (hrs : ∀ r ∈ rs, r ∉ kept := by decide) :
    Mid S s w :=
  h.keep (S' := S) o.keep (by rw [o.mem]; exact h.mem) (by rw [o.mem]; exact h.sv) hrs

/-- Writes of the frame apart from the slots keep `Mid`'s memory. -/
theorem Mid.frameMem (h : Mid S s t) {f n : Nat} {m : Mem}
    (he : oEnd ≤ f ∨ f + n ≤ oSave) (hen : f + n ≤ frameBytes) (hm : Frame [⟨fb s + BitVec.ofNat 64 f, n⟩] t.mem m) :
    Frame (kR s :: S) s.mem m ∧ Spill.Saved (fb s) s.gpr saved m := by
  refine ⟨h.mem.trans (hm.sub fun r hr => ?_), h.sv.frame hm fun p hp r hr => ?_⟩
  · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s hen⟩
  · have := saved_offs p hp
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (by unfold oEnd oSave at *; omega) (by unfold oEnd at *; omega)
      (by unfold frameBytes at hen; omega)

end

/-- A buffer of the caller that the function does not write. -/
theorem bytes_of_frame {s : State} {rs : List Region} {m : Mem} (hf : Frame rs s.mem m) {p : Addr}
    {len : Nat} (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, len⟩ r) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) hd hl (List.mem_range.mp hi)

/-- The saves, from the state after the allocation (`u`): `t0` holds the
frame's base, `s0`–`s9` and the return address are in their slots, and
memory is changed only in the frame. -/
theorem save_ok {s u : State} (hsp : u.sp = fb s) (hwr : u.wr = frR s :: s.wr) (hal : (fb s).toNat % 8 = 0)
    (hm : Frame [kR s] s.mem u.mem) (hg : ∀ r ∈ preserved ++ ([.ra] : List Reg), u.gpr r = s.gpr r)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ v, Kept [.t0] u v → v.gpr .t0 = fb s → Frame [kR s] s.mem v.mem →
      Spill.Saved (fb s) s.gpr saved v.mem → WP isa (.block rest) v Q) :
    WP isa (.block (spill ++ rest)) u Q := by
  simp only [spill, List.cons_append, List.nil_append]
  refine wp_addSp fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  refine Spill.save_ok (b := .t0) (l := saved) (by rw [e₁]; exact hal) saved_ho (fun p hp => ?_) ?_
  · have := saved_offs p hp
    rw [e₁, o₁.wr, hwr]; exact in_fr s _ (by unfold oEnd frameBytes at *; omega)
  refine k _ ⟨fun r hr => o₁.gpr r hr, o₁.rd, o₁.wr, o₁.sp⟩ e₁ ?_ ?_
  · show Frame [kR s] s.mem (Spill.saveMem u₁.mem (u₁.gpr .t0) u₁.gpr saved)
    rw [e₁, o₁.mem]
    exact hm.trans ((Spill.saveMem_frame_base (n := frameBytes) (fun p hp => by
      have := saved_offs p hp; unfold oEnd frameBytes at *; omega) (by decide) _ _ _).sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, frR_sub s⟩)
  · show Spill.Saved (fb s) s.gpr saved (Spill.saveMem u₁.mem (u₁.gpr .t0) u₁.gpr saved)
    rw [e₁]
    refine fun p hp => (Spill.saveMem_saved (by decide) _ _ _ p hp).trans ?_
    have h0 : p.1 ∉ [Reg.t0] := by revert p; decide
    rw [o₁.gpr _ h0, hg _ (by revert p; decide)]

/-- What the restores need: the frame, our caller's registers and return
address in their slots, and the other callee-saved registers as on entry. -/
structure Saves (s t : State) : Prop where
  sp : t.sp = fb s
  wr : t.wr = frR s :: s.wr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  sv : Spill.Saved (fb s) s.gpr saved t.mem

theorem Mid.saves {S : List Region} {s t : State} (h : Mid S s t) :
    Saves s t :=
  ⟨h.sp, h.wr, h.hi, h.sv⟩

/-- The restores: the caller's registers and return address are back, and
`a0` and memory are kept. -/
theorem restore_ok {s w : State} (h : DPre s) (hm : Saves s w) :
    WP isa (.block restore) w fun w' =>
      abiPreserved s (freed frameBytes w') ∧ w'.gpr .a0 = w.gpr .a0 ∧ w'.mem = w.mem := by
  rw [restore_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun w₁ o₁ e₁ => ?_
  rw [hm.sp, BitVec.add_zero] at e₁
  refine WP.mono (Spill.restore_wp (b := .t0) (l := saved) (B := fb s) (g := s.gpr) (by
      have := fb_al8 h (d := 0) (by decide); rwa [BitVec.add_zero] at this)
    e₁ saved_ho (by decide)
    (fun p hp => by
      have := saved_offs p hp
      rw [o₁.rd, o₁.wr, hm.wr]; exact in_fr' s _ _ (by unfold oEnd frameBytes at *; omega))
    (by rw [o₁.mem]; exact hm.sv)) fun w' hr => ⟨⟨fun r hr' => ?_, ?_, ?_⟩, ?_, ?_⟩
  · show w'.gpr r = s.gpr r
    rcases preserved_split hr' with h | h
    · exact hr.gpr_of (.inl h)
    · have h0 : r ∉ saved.map Prod.fst := by revert r; decide
      have h2 : r ∉ [Reg.t0] := by revert r; decide
      rw [hr.other r h0, o₁.gpr r h2]; exact hm.hi r h
  · show w'.sp + BitVec.ofNat 64 frameBytes = s.sp
    rw [hr.sp, o₁.sp, hm.sp, BitVec.sub_add_cancel]
  · show w'.gpr .ra = s.gpr .ra
    exact hr.gpr_of (.inl (by simp [saved]))
  · show w'.gpr .a0 = w.gpr .a0
    rw [hr.other .a0 (by decide), o₁.get .a0]
  · rw [hr.mem, o₁.mem]

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64

/-! ## Our stack arguments -/

theorem arg_frame {s : State} (h : DPre s) {m : Mem} (hm : Frame [kR s] s.mem m) {j : Nat} (hj : j < 15) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  hm.readW (in_aR hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ka.symm) (by decide)

theorem arg_in {s t : State} (h : DPre s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 15) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 := by
  rw [hrd, h.hrd]
  exact ⟨_, List.mem_append_left _ (by simp), in_aR hj⟩

theorem arg_al {s : State} (h : DPre s) (j : Nat) : (stackArgAddr s j).toNat % 8 = 0 := by
  simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := s.sp.isLt; have := h.sp16
  omega

/-! ## The setup -/

/-- The call's stack arguments. -/
abbrev psaR (s : State) : Region := ⟨fb s, 96⟩

/-- At the call of `vg_rsa_private_checked`. -/
structure AtCall (s t : State) : Prop extends Mid [] s t where
  a0 : t.gpr .a0 = s.gpr .a0
  a1 : t.gpr .a1 = s.gpr .a4
  a2 : t.gpr .a2 = s.gpr .a3
  a3 : t.gpr .a3 = s.gpr .a4
  a4 : t.gpr .a4 = s.gpr .a5
  a5 : t.gpr .a5 = s.gpr .a6
  a6 : t.gpr .a6 = stackArg s 1
  a7 : t.gpr .a7 = s.gpr .a4
  psa : ∀ i < 12, t.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (3 + i)

/-- After copying the first `n` stack arguments, from `w`. -/
structure CI (s w : State) (n : Nat) (t : State) : Prop where
  keep : Kept [.t1] w t
  mem : Frame [psaR s] w.mem t.mem
  psa : ∀ i < n, t.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (3 + i)

theorem psa_sub (s : State) : Region.Sub (psaR s) (kR s) := by
  have := frame_sub s (d := 0) (n := 96) (by decide)
  rwa [BitVec.add_zero] at this

theorem copy_step {s w : State} (h : DPre s) (hw0 : w.gpr .t0 = fb s) (hw6 : w.gpr .t6 = stackArgAddr s 0)
    (hrd : w.rd = s.rd) (hwr : w.wr = frR s :: s.wr) (hm : Frame [kR s] s.mem w.mem) {n : Nat} (hn : n < 12)
    {t : State} (hc : CI s w n t) : WP isa (.block (copyArg n)) t (CI s w (n + 1)) := by
  have hmt : Frame [kR s] s.mem t.mem := hm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub s⟩)
  unfold copyArg
  refine wp_ld (a := stackArgAddr s (3 + n)) (by rw [hc.keep.get .t6, hw6, ← stackArgAddr_eq]) (arg_al h _)
    (arg_in h (hc.keep.rd.trans hrd) (by omega)) (fun t₁ o₁ e₁ => ?_) (by omega)
  refine wp_sd (a := fb s + BitVec.ofNat 64 (8 * n)) (by rw [o₁.get .t0, hc.keep.get .t0, hw0])
    (fb_al8 h (by omega)) (by rw [o₁.wr, hc.keep.wr, hwr]; exact in_fr s _ (by unfold frameBytes; omega))
    (fun t₂ m₂ => wp_nil ?_) (by omega)
  rw [arg_frame h hmt (by omega)] at e₁
  rw [e₁] at m₂
  refine ⟨(hc.keep.trans (o₁.keep.trans m₂.keep)).mono, ?_, fun i hi => ?_⟩
  · rw [m₂.mem, o₁.mem]
    exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base (fb s) (d := 8 * n) (n := 8) (k := 96)
      (by omega) (by omega))
  · rw [m₂.mem, o₁.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
      exact hc.psa i hi
    · rw [Mem.readW_writeW_self64]

theorem copies_ok {s w : State} (h : DPre s) (hw0 : w.gpr .t0 = fb s) (hw6 : w.gpr .t6 = stackArgAddr s 0)
    (hrd : w.rd = s.rd) (hwr : w.wr = frR s :: s.wr) (hm : Frame [kR s] s.mem w.mem) :
    WP isa (.block ((List.range 12).flatMap copyArg)) w (CI s w 12) :=
  wp_range_flatMap (M := isa) (CI s w) (fun _ _ hn hc => copy_step h hw0 hw6 hrd hwr hm hn hc) 12
    (Nat.le_refl _) w ⟨Kept.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem setup_ok {s : State} (h : DPre s) :
    WP isa (.block setup) (allocd frameBytes s) (AtCall s) := by
  have hfa := fb_al h
  have e : setup = spill ++ (keeps ++ (List.range 12).flatMap copyArg ++ privRegs) := by
    simp only [setup, save_eq, List.append_assoc]
  rw [e]
  refine save_ok (s := s) (u := allocd frameBytes s) rfl rfl (by omega) (Frame.refl _ _) (fun _ _ => rfl)
    fun v kv v0 fv sv => ?_
  have gv : ∀ r, r ∉ [Reg.t0] → v.gpr r = s.gpr r := fun r hr => kv.gpr r hr
  have rdv : v.rd = s.rd := kv.rd
  have wrv : v.wr = frR s :: s.wr := kv.wr
  have spv : v.sp = fb s := kv.sp
  rw [List.append_assoc]
  simp only [keeps, argBase, List.cons_append, List.nil_append]
  refine wp_addSp (imm := frameBytes) (fun v₁ o₁ e₁ => wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ =>
    wp_mov fun v₄ o₄ e₄ => wp_mov fun v₅ o₅ e₅ => ?_) (by decide)
  have P₅ : Only [.t6, .s1, .s2, .s3, .s4] v v₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have t6₅ : v₅.gpr .t6 = stackArgAddr s 0 := by
    rw [o₅.get .t6, o₄.get .t6, o₃.get .t6, o₂.get .t6, e₁, spv, stackArgAddr_fb]; rfl
  refine wp_ld (a := stackArgAddr s 0) (by rw [t6₅, BitVec.add_zero]) (arg_al h 0)
    (arg_in h (P₅.rd.trans rdv) (j := 0) (by decide)) fun v₆ o₆ e₆ => ?_
  refine wp_ld (a := stackArgAddr s 1) (by rw [o₆.get .t6, t6₅]; exact (stackArgAddr_eq s 1).symm) (arg_al h 1)
    (arg_in h (o₆.rd.trans (P₅.rd.trans rdv)) (j := 1) (by decide)) fun v₇ o₇ e₇ => ?_
  refine wp_ld (a := stackArgAddr s 13) (by rw [o₇.get .t6, o₆.get .t6, t6₅]; exact (stackArgAddr_eq s 13).symm) (arg_al h 13)
    (arg_in h (o₇.rd.trans (o₆.rd.trans (P₅.rd.trans rdv))) (j := 13) (by decide)) (fun w o₈ e₈ => ?_)
    (by decide)
  have P : Only [.t6, .s1, .s2, .s3, .s4, .s5, .s6, .s0] v w := (P₅.trans (o₆.trans (o₇.trans o₈))).mono
  rw [P₅.mem, arg_frame h fv (j := 0) (by decide)] at e₆
  rw [o₆.mem, P₅.mem, arg_frame h fv (j := 1) (by decide)] at e₇
  rw [o₇.mem, o₆.mem, P₅.mem, arg_frame h fv (j := 13) (by decide)] at e₈
  have M : Mid [] s w := {
    sp := by rw [P.sp, spv]
    rd := by rw [P.rd, rdv]
    wr := by rw [P.wr, wrv]
    s0 := e₈
    s1 := by
      rw [o₈.get .s1, o₇.get .s1, o₆.get .s1, o₅.get .s1, o₄.get .s1, o₃.get .s1, e₂, o₁.get .a4,
        gv .a4 (by decide)]
    s2 := by
      rw [o₈.get .s2, o₇.get .s2, o₆.get .s2, o₅.get .s2, o₄.get .s2, e₃, o₂.get .a0, o₁.get .a0,
        gv .a0 (by decide)]
    s3 := by
      rw [o₈.get .s3, o₇.get .s3, o₆.get .s3, o₅.get .s3, e₄, o₃.get .a2, o₂.get .a2, o₁.get .a2,
        gv .a2 (by decide)]
    s4 := by
      rw [o₈.get .s4, o₇.get .s4, o₆.get .s4, e₅, o₄.get .a7, o₃.get .a7, o₂.get .a7, o₁.get .a7,
        gv .a7 (by decide)]
    s5 := by rw [o₈.get .s5, o₇.get .s5, e₆]
    s6 := by rw [o₈.get .s6, e₇]
    hi := fun r hr => by rw [P.gpr r (by revert r; decide), gv r (by revert r; decide)]
    mem := by rw [P.mem]; exact fv
    sv := by rw [P.mem]; exact sv }
  have w0 : w.gpr .t0 = fb s := by rw [P.get .t0, v0]
  have w6 : w.gpr .t6 = stackArgAddr s 0 := by rw [o₈.get .t6, o₇.get .t6, o₆.get .t6, t6₅]
  rw [WP.block_append_iff]
  refine WP.mono (copies_ok h w0 w6 M.rd M.wr M.mem) fun x hc => ?_
  have hf := M.frameMem (f := 0) (n := 96) (.inr (by decide)) (by decide)
    (by rw [BitVec.add_zero]; exact hc.mem)
  have M' : Mid [] s x := M.keep hc.keep hf.1 hf.2
  have gw : ∀ r ∈ [Reg.a0, .a3, .a5, .a6], x.gpr r = s.gpr r := fun r hr => by
    rw [hc.keep.gpr r (by revert r; decide), P.gpr r (by revert r; decide), gv r (by revert r; decide)]
  unfold privRegs
  refine wp_mov fun x₁ q₁ f₁ => wp_mov fun x₂ q₂ f₂ => wp_mov fun x₃ q₃ f₃ => wp_mov fun x₄ q₄ f₄ =>
    wp_mov fun x₅ q₅ f₅ => wp_mov fun x₆ q₆ f₆ => wp_mov fun x₇ q₇ f₇ => wp_nil ?_
  have O : Only [.a1, .a2, .a3, .a4, .a5, .a6, .a7] x x₇ :=
    (q₁.trans (q₂.trans (q₃.trans (q₄.trans (q₅.trans (q₆.trans q₇)))))).mono
  exact {
    toMid := M'.only O
    a0 := by rw [O.get .a0, gw .a0 (by decide)]
    a1 := by rw [q₇.get .a1, q₆.get .a1, q₅.get .a1, q₄.get .a1, q₃.get .a1, q₂.get .a1, f₁, M'.s1]
    a2 := by rw [q₇.get .a2, q₆.get .a2, q₅.get .a2, q₄.get .a2, q₃.get .a2, f₂, q₁.get .a3, gw .a3 (by decide)]
    a3 := by rw [q₇.get .a3, q₆.get .a3, q₅.get .a3, q₄.get .a3, f₃, q₂.get .s1, q₁.get .s1, M'.s1]
    a4 := by rw [q₇.get .a4, q₆.get .a4, q₅.get .a4, f₄, q₃.get .a5, q₂.get .a5, q₁.get .a5, gw .a5 (by decide)]
    a5 := by rw [q₇.get .a5, q₆.get .a5, f₅, q₄.get .a6, q₃.get .a6, q₂.get .a6, q₁.get .a6, gw .a6 (by decide)]
    a6 := by
      rw [q₇.get .a6, f₆, q₅.get .s6, q₄.get .s6, q₃.get .s6, q₂.get .s6, q₁.get .s6, M'.s6]
    a7 := by
      rw [f₇, q₆.get .s1, q₅.get .s1, q₄.get .s1, q₃.get .s1, q₂.get .s1, q₁.get .s1, M'.s1]
    psa := fun i hi => by rw [O.mem]; exact hc.psa i hi }

/-! ## The call -/

/-- The regions the call reads and writes. -/
abbrev callRd (s : State) : List Region := [nR s, eR s, iR s, pR s, qR s, dpR s, dqR s, qiR s, psaR s]

abbrev callWr (s : State) : List Region := [oR s, sR s]

/-- The call's narrowed entry state. -/
abbrev callE (s t : State) : State := t.callEntry.withRegions (callRd s) (callWr s)

theorem callE_gpr (s t : State) {r : Reg} (hr : r ∉ linkRegs := by decide) : (callE s t).gpr r = t.gpr r :=
  State.callEntry_gpr t hr

theorem callE_stackArg {s t : State} (A : AtCall s t) {i : Nat} (hi : i < 12) :
    stackArg (callE s t) i = stackArg s (3 + i) := by
  show t.mem.readW (stackArgAddr (callE s t) i) 64 = _
  rw [stackArgAddr, show (callE s t).sp = fb s from A.sp]
  exact A.psa i hi

theorem preP_entry {s t : State} (h : DPre s) (A : AtCall s t) : Rsa.RISCV64.Priv.PreP (callE s t) := by
  have hk := h.k2
  have fbt := fb_toNat h
  have kbt := kb_toNat h
  unfold stackBytes frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at kbt
  unfold frameBytes at fbt
  have sa := fun i hi => callE_stackArg A (i := i) hi
  have hsp : (callE s t).sp = fb s := A.sp
  have cs := callee_sub s
  have ps := psa_sub s
  have hK : Rsa.RISCV64.Priv.kR (callE s t) = ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ := by
    simp only [Rsa.RISCV64.Priv.kR, Rsa.RISCV64.Priv.fb, hsp, fb_eq, BitVec.add_sub_cancel]
  have ka : Region.Disjoint ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ (psaR s) := by
    show Region.Disjoint _ ⟨fb s, 96⟩
    rw [fb_eq]
    exact (Offset.disjoint_base _ (by unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega)
      (by unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega)).symm
  have cs' : Region.Sub ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ (kR s) := by
    have := cs; rwa [fb_eq, BitVec.add_sub_cancel] at this
  have g0 : (callE s t).gpr .a0 = s.gpr .a0 := (callE_gpr s t).trans A.a0
  have g1 : (callE s t).gpr .a1 = s.gpr .a4 := (callE_gpr s t).trans A.a1
  have g2 : (callE s t).gpr .a2 = s.gpr .a3 := (callE_gpr s t).trans A.a2
  have g3 : (callE s t).gpr .a3 = s.gpr .a4 := (callE_gpr s t).trans A.a3
  have g4 : (callE s t).gpr .a4 = s.gpr .a5 := (callE_gpr s t).trans A.a4
  have g5 : (callE s t).gpr .a5 = s.gpr .a6 := (callE_gpr s t).trans A.a5
  have g6 : (callE s t).gpr .a6 = stackArg s 1 := (callE_gpr s t).trans A.a6
  have g7 : (callE s t).gpr .a7 = s.gpr .a4 := (callE_gpr s t).trans A.a7
  have hO : Rsa.RISCV64.Priv.oR (callE s t) = oR s := by simp only [Rsa.RISCV64.Priv.oR, g0, g1, oR, h.h1]
  have hN : Rsa.RISCV64.Priv.nR (callE s t) = nR s := by simp only [Rsa.RISCV64.Priv.nR, g2, g3]
  have hE : Rsa.RISCV64.Priv.eR (callE s t) = eR s := by simp only [Rsa.RISCV64.Priv.eR, g4, g5]
  have hI : Rsa.RISCV64.Priv.iR (callE s t) = iR s := by simp only [Rsa.RISCV64.Priv.iR, g6, g7, iR, h.hi]
  have hP : Rsa.RISCV64.Priv.pR (callE s t) = pR s := by
    simp only [Rsa.RISCV64.Priv.pR, sa 0 (by decide), sa 1 (by decide)]
  have hQ : Rsa.RISCV64.Priv.qR (callE s t) = qR s := by
    simp only [Rsa.RISCV64.Priv.qR, sa 2 (by decide), sa 3 (by decide)]
  have hDP : Rsa.RISCV64.Priv.dpR (callE s t) = dpR s := by
    simp only [Rsa.RISCV64.Priv.dpR, sa 4 (by decide), sa 5 (by decide)]
  have hDQ : Rsa.RISCV64.Priv.dqR (callE s t) = dqR s := by
    simp only [Rsa.RISCV64.Priv.dqR, sa 6 (by decide), sa 7 (by decide)]
  have hQI : Rsa.RISCV64.Priv.qiR (callE s t) = qiR s := by
    simp only [Rsa.RISCV64.Priv.qiR, sa 8 (by decide), sa 9 (by decide)]
  have hS : Rsa.RISCV64.Priv.sR (callE s t) = sR s := by
    simp only [Rsa.RISCV64.Priv.sR, sa 10 (by decide), sa 11 (by decide)]
  have hA : Rsa.RISCV64.Priv.aR (callE s t) = psaR s := by
    simp only [Rsa.RISCV64.Priv.aR, stackArgAddr, hsp, Nat.mul_zero, BitVec.add_zero]
  have s0 := sa 0 (by decide)
  have s1 := sa 1 (by decide)
  have s2 := sa 2 (by decide)
  have s3 := sa 3 (by decide)
  have s4 := sa 4 (by decide)
  have s5 := sa 5 (by decide)
  have s6 := sa 6 (by decide)
  have s7 := sa 7 (by decide)
  have s8 := sa 8 (by decide)
  have s9 := sa 9 (by decide)
  have s10 := sa 10 (by decide)
  have s11 := sa 11 (by decide)
  have wo' : (s.gpr .a0).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 := h.h1 ▸ h.wo
  have wi' : (stackArg s 1).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 := h.hi ▸ h.wi
  have fa := fb_al h
  refine ⟨by rw [hsp]; exact fa, by rw [hsp]; unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega,
    by rw [hsp]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN, hE, hI, hP, hQ, hDP, hDQ, hQI, hA]; rfl
  · rw [hO, hS]; rfl
  · rw [hO, hN]; exact h.on
  · rw [hO, hE]; exact h.oe
  · rw [hO, hI]; exact h.oi
  · rw [hO, hP]; exact h.op
  · rw [hO, hQ]; exact h.oq
  · rw [hO, hDP]; exact h.odp
  · rw [hO, hDQ]; exact h.odq
  · rw [hO, hQI]; exact h.oqi
  · rw [hO, hS]; exact h.os
  · rw [hO, hA]; exact (h.ko.sub_left ps).symm
  · rw [hN, hS]; exact h.ns
  · rw [hE, hS]; exact h.es
  · rw [hI, hS]; exact h.is
  · rw [hP, hS]; exact h.ps
  · rw [hQ, hS]; exact h.qs
  · rw [hDP, hS]; exact h.dps
  · rw [hDQ, hS]; exact h.dqs
  · rw [hQI, hS]; exact h.qis
  · rw [hS, hA]; exact (h.ks.sub_left ps).symm
  · rw [hK, hO]; exact h.ko.sub_left cs'
  · rw [hK, hN]; exact h.kn.sub_left cs'
  · rw [hK, hE]; exact h.ke.sub_left cs'
  · rw [hK, hI]; exact h.ki.sub_left cs'
  · rw [hK, hP]; exact h.kp.sub_left cs'
  · rw [hK, hQ]; exact h.kq.sub_left cs'
  · rw [hK, hDP]; exact h.kdp.sub_left cs'
  · rw [hK, hDQ]; exact h.kdq.sub_left cs'
  · rw [hK, hQI]; exact h.kqi.sub_left cs'
  · rw [hK, hS]; exact h.ks.sub_left cs'
  · rw [hK, hA]; exact ka
  · rw [g0, g1]; exact wo'
  · rw [g2, g3]; exact h.wn
  · rw [g4, g5]; exact h.we
  · rw [g6, g7]; exact wi'
  · rw [s0, s1]; exact h.wp
  · rw [s2, s3]; exact h.wq
  · rw [s4, s5]; exact h.wdp
  · rw [s6, s7]; exact h.wdq
  · rw [s8, s9]; exact h.wqi
  · rw [s10, s11]; exact h.ws
  · rw [g3]; exact h.k1
  · rw [g3]; exact h.k2
  · rw [g1, g3]
  · rw [g7, g3]
  · rw [g5]; exact h.e1
  · rw [g5, g3]; exact h.e2
  · rw [s1]; exact h.p1
  · rw [s1, g3]; exact h.p2
  · rw [s3]; exact h.q1
  · rw [s3, g3]; exact h.q2
  · rw [s5, s1]; exact h.h8
  · rw [s9, s1]; exact h.h12
  · rw [s7, s3]; exact h.h10
  · rw [g3, s11]; exact h.hs
  · rw [s10]; exact h.al

/-- The outcome of `vg_rsa_private_checked` of the input, from the caller's
buffers. -/
abbrev privOut (s u : State) : Prop :=
  Spec.Rsa.writtenOutcome u.mem (s.gpr .a0) (s.gpr .a4).toNat ((u.gpr .a0).setWidth 32)
    (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .a4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat))

/-- After the call. -/
structure AtRet (s u : State) : Prop extends Mid [oR s, sR s] s u where
  out : privOut s u

theorem call_covers {s t : State} (h : DPre s) (A : AtCall s t) :
    Covers (callRd s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  have hw : Covers (callWr s) t.wr := by
    rw [A.wr, h.hwr]
    exact Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, h.hrd]
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · have := in_fr s s.wr (d := 0) (n := 96) (by decide)
    rw [BitVec.add_zero] at this
    exact Covers.right (Covers.one this)

theorem priv_sdepth : sdepth Impl.Rsa.RISCV64.Priv.code = Impl.Rsa.RISCV64.Priv.frameBytes := by decide +kernel

theorem call_ok {s t : State} (h : DPre s) (A : AtCall s t) {Q : State → Prop}
    (hQ : ∀ u, AtRet s u → Q u) : WP isa privCall t Q := by
  obtain ⟨hc, hw⟩ := call_covers h A
  have cs := callee_sub s
  unfold privCall
  refine WP.callAny (k := Rsa.RISCV64.Priv.fnContract) Rsa.RISCV64.Priv.code_correct
    (Rsa.RISCV64.Priv.pre_of_preP (preP_entry h A)) hc hw
    (fun u hrd hwr hsp hf hpres hpost => hQ u ?_) (by rw [priv_sdepth]; decide)
  have hb : below t.sp (sdepth Impl.Rsa.RISCV64.Priv.code) =
      ⟨fb s - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes⟩ := by
    rw [priv_sdepth, A.sp]
  rw [hb] at hf
  simp only [callWr, List.cons_append, List.nil_append] at hf
  have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
  have ap : ∀ {d : Nat}, d + 8 ≤ frameBytes → ∀ r ∈ [oR s, sR s, (⟨fb s - BitVec.ofNat 64
      Impl.Rsa.RISCV64.Priv.frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
    intro d hd r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.ko.sub_left (frame_sub s hd)
    · exact h.ks.sub_left (frame_sub s hd)
    · rw [fb_eq, BitVec.add_sub_cancel, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact Offset.disjoint_base _ (by omega) (by unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at *; omega)
  have g : ∀ r ∈ kept, u.gpr r = t.gpr r := fun r hr => hp r (by revert r; decide)
  refine ⟨A.toMid.of g (hsp.trans rfl) hrd hwr ?_ (A.sv.frame hf fun p hp' r hr =>
      ap (by have := saved_offs p hp'; unfold oEnd frameBytes at *; omega) r hr), ?_⟩
  · refine A.mem.sub (fun r hr => ?_) |>.trans (hf.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self .., cs⟩
  · have sa := fun i hi => callE_stackArg A (i := i) hi
    simp only [Rsa.RISCV64.Priv.fnContract, Rsa.RISCV64.Priv.fnPost, State.withRegions_mem,
      State.withRegions_gpr, State.callEntry_mem, callE_gpr s t (r := .a0), callE_gpr s t (r := .a2),
      callE_gpr s t (r := .a3), callE_gpr s t (r := .a4), callE_gpr s t (r := .a5), callE_gpr s t (r := .a6),
      A.a0, A.a2, A.a3, A.a4, A.a5, A.a6, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 3 (by decide),
      sa 4 (by decide), sa 6 (by decide), sa 8 (by decide), Nat.reduceAdd] at hpost
    have hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) A.mem (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    have di : Region.Disjoint ⟨stackArg s 1, (s.gpr .a4).toNat⟩ (kR s) := by
      have := h.ki.symm; simp only [iR, h.hi] at this; exact this
    rw [hb h.kn.symm (by have := h.wn; omega), hb h.ke.symm (by have := h.we; omega),
      hb di (by have := h.wi; have := h.hi; omega), hb h.kp.symm (by have := h.wp; omega),
      hb h.kq.symm (by have := h.wq; omega),
      hb (h.h8 ▸ h.kdp.symm) (by have := h.wdp; omega), hb (h.h10 ▸ h.kdq.symm) (by have := h.wdq; omega),
      hb (h.h12 ▸ h.kqi.symm) (by have := h.wqi; omega)] at hpost
    exact hpost

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64 VG.WriteBytes
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## `scratch` -/

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

/-- `scratch + a`. -/
abbrev scA (s : State) (a : Nat) : Addr := stackArg s 13 + BitVec.ofNat 64 a

/-- The bytes of `scratch` the function uses after the call. -/
def scrBytes : Nat := 2576

section
variable {s : State} (h : DPre s)
include h

theorem scr_le : scrBytes ≤ (stackArg s 14).toNat * 8 := by
  have := h.hs; have := h.k1; unfold Spec.Rsa.scratchWords scrBytes at *; omega

theorem scSub {a l : Nat} (ha : a + l ≤ scrBytes) : Region.Sub ⟨scA s a, l⟩ (sR s) :=
  Offset.sub_base _ (by have := scr_le h; omega)

theorem scContains {a l : Nat} (ha : a + l ≤ scrBytes) : (sR s).Contains (scA s a) l :=
  Offset.contains_base _ (by have := scr_le h; omega) (by unfold scrBytes at ha; omega)

theorem scIn {t : State} (hwr : t.wr = frR s :: s.wr) {a l : Nat} (ha : a + l ≤ scrBytes) :
    InRegions t.wr (scA s a) l := by
  rw [hwr, h.hwr]; exact ⟨sR s, by simp, scContains h ha⟩

theorem scCov {t : State} (hwr : t.wr = frR s :: s.wr) {a l : Nat} (ha : a + l ≤ scrBytes) :
    Covers [⟨scA s a, l⟩] t.wr :=
  Covers.one (scIn h hwr ha)

theorem scByte {t : State} (hwr : t.wr = frR s :: s.wr) {a n : Nat} (ha : a + n ≤ scrBytes) :
    ∀ i < n, InRegions t.wr (scA s a + BitVec.ofNat 64 i) 1 := fun i hi => by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact scIn h hwr (by omega)

end

/-! ## After the call -/

/-- The low word of `x`, zero-extended. -/
abbrev zx (x : BitVec 64) : BitVec 64 := (x.setWidth 32).setWidth 64

theorem zext_eq (x : BitVec 64) : x <<< 32 >>> 32 = zx x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth]
  omega

/-- From the call on: `Mid` with `out` and `scratch` written, `R` in `s7` and
`EM` in `out`. -/
structure Post (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop extends Mid [oR s, sR s] s t where
  r : t.gpr .s7 = R
  em : Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a4).toNat = EM

section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte}
include h

/-- The callees' frames, below ours. -/
abbrev lowR (s : State) : Region :=
  ⟨fb s - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes⟩

omit h in
theorem slot_low (s : State) {d : Nat} (hd : d + 8 ≤ frameBytes) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ (lowR s) := by
  simp only [lowR]
  rw [fb_eq, BitVec.add_sub_cancel, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact Offset.disjoint_base _ (by omega) (by unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at *; omega)

/-- `Post` is kept by code writing registers `Mid` does not keep but `s7`,
`scratch` and the callees' frames. -/
theorem Post.keep {t w : State} (hp : Post s R EM t) {rs : List Reg} (o : Kept rs t w) {ws : List Region}
    (hf : Frame ws t.mem w.mem) (hs : ∀ r ∈ ws, Region.Sub r (sR s) ∨ Region.Sub r (lowR s))
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) (h7 : Reg.s7 ∉ rs := by decide) : Post s R EM w := by
  have cs := callee_sub s
  refine ⟨hp.toMid.keep o (hp.mem.trans (hf.sub fun r hr => ?_)) (hp.sv.frame hf fun q hq r hr => ?_) hrs,
    (o.gpr _ h7).trans hp.r, ?_⟩
  · rcases hs r hr with hr' | hr'
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), hr'⟩
    · exact ⟨_, List.mem_cons_self .., sub_trans hr' cs⟩
  · have := saved_offs q hq
    rcases hs r hr with hr' | hr'
    · exact (h.ks.sub_left (frame_sub s (by unfold oEnd frameBytes at *; omega))).sub_right hr'
    · exact (slot_low s (by unfold oEnd frameBytes at *; omega)).sub_right hr'
  · rw [← hp.em]
    exact bytes_of_frame (s := t) hf (fun r hr => by
      rcases hs r hr with hr' | hr'
      · have := h.os.sub_right hr'; simp only [oR, h.h1] at this; exact this
      · have := (h.ko.symm.sub_right cs).sub_right hr'; simp only [oR, h.h1] at this; exact this)
      (by have := h.wo; have := h.h1; omega)


/-! ## `D` -/

omit h in
theorem W_nil (s : State) : W s [] s :=
  ⟨Kept.refl _ _, (writeBytes_nil _ _).symm, by rw [List.length_nil, BitVec.add_zero]⟩

omit h in
theorem gpr_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

omit h in
/-- Writing over the same bytes. -/
theorem writeBytes_writeBytes (m : Mem) (q : Addr) {xs ys : List Byte} (hl : xs.length = ys.length) :
    writeBytes (writeBytes m q xs) q ys = writeBytes m q ys := by
  funext a
  simp only [writeBytes]
  by_cases h1 : (a - q).toNat < ys.length
  · simp only [h1, ite_true]
  · simp only [h1, ite_false, hl]

omit h in
/-- `k` zeros, then `ys` written over their end. -/
theorem zeros_then (m : Mem) (q : Addr) {k : Nat} {ys : List Byte} (hl : ys.length ≤ k) (hk : k < 2 ^ 64) :
    Spec.Rsa.bytesAt (writeBytes (writeBytes m q (List.replicate k 0))
      (q + BitVec.ofNat 64 (k - ys.length)) ys) q k = List.replicate (k - ys.length) 0 ++ ys := by
  have e : List.replicate k (0 : Byte) = List.replicate (k - ys.length) 0 ++ List.replicate ys.length 0 := by
    rw [List.replicate_append_replicate, Nat.sub_add_cancel hl]
  have e2 : writeBytes m q (List.replicate k 0) = writeBytes (writeBytes m q (List.replicate (k - ys.length) 0))
      (q + BitVec.ofNat 64 (k - ys.length)) (List.replicate ys.length 0) := by
    have := writeBytes_append m q (List.replicate (k - ys.length) (0 : Byte)) (List.replicate ys.length 0)
      (by simp; omega)
    rw [List.length_replicate] at this
    rw [e, ← this]
  have e3 : writeBytes (writeBytes m q (List.replicate (k - ys.length) 0)) (q + BitVec.ofNat 64 (k - ys.length)) ys =
      writeBytes m q (List.replicate (k - ys.length) 0 ++ ys) := by
    have := writeBytes_append m q (List.replicate (k - ys.length) (0 : Byte)) ys (by simp; omega)
    rwa [List.length_replicate] at this
  rw [e2, writeBytes_writeBytes _ _ (by simp), e3]
  have := Proof.RsaPkcs1Sig.bytesAt_writeBytes m q (List.replicate (k - ys.length) 0 ++ ys) (by simp; omega)
  rwa [List.length_append, List.length_replicate, Nat.sub_add_cancel hl] at this

/-- The private exponent's bytes. -/
abbrev dBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat

/-- After `dBuild`: `D` at `scratch + sD`. -/
structure DB (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop extends Post s R EM t where
  D : Spec.Rsa.bytesAt t.mem (scA s sD) (s.gpr .a4).toNat = Spec.Rsa.i2osp (Spec.Rsa.os2ip (dBytes s)) (s.gpr .a4).toNat

theorem dBuild_ok {u : State} (A : AtRet s u) :
    WP isa dBuild u (DB s (zx (u.gpr .a0)) (Spec.Rsa.bytesAt u.mem (s.gpr .a0) (s.gpr .a4).toNat)) := by
  have hk := h.k2
  have hk1 := h.k1
  have hd1 := h.d1
  have hd2 := h.d2
  unfold dBuild dZeros
  refine WP.seq (wp_sll fun u₁ o₁ e₁ => wp_srl fun u₂ o₂ e₂ => wp_addi (imm := sD) (fun u₃ o₃ e₃ =>
    wp_mov fun u₄ o₄ e₄ => wp_li (imm := 0) (by decide) fun w o₅ e₅ => wp_nil ?_) (by decide))
  have O : Only [.s7, .a1, .t5, .t0] u w := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have P : Post s (zx (u.gpr .a0)) (Spec.Rsa.bytesAt u.mem (s.gpr .a0) (s.gpr .a4).toNat) w :=
    ⟨A.toMid.only O, by rw [o₅.get .s7, o₄.get .s7, o₃.get .s7, e₂, e₁, zext_eq], by rw [O.mem]⟩
  have w1 : w.gpr .a1 = scA s sD := by rw [o₅.get .a1, o₄.get .a1, e₃, o₂.get .s0, o₁.get .s0, A.s0]
  have w5 : w.gpr .t5 = BitVec.ofNat 64 (s.gpr .a4).toNat := by
    rw [o₅.get .t5, e₄, o₃.get .s1, o₂.get .s1, o₁.get .s1, A.s1, ← gpr_ofNat]
  have hb : Buf w (s.gpr .a4).toNat := fun i hi => by
    rw [w1]; exact scByte h P.wr (a := sD) (n := (s.gpr .a4).toNat) (by unfold sD scrBytes; omega) i hi
  refine WP.seq (WP.mono (fillLoop_ok hb (by omega) (acc := []) (by omega) (by simp) (W_nil w) 0
    (by rw [e₅]; rfl) w5) fun t₁ ⟨⟨K₁, m₁, _⟩, _⟩ => ?_)
  rw [List.nil_append, w1] at m₁
  have P₁ := P.keep h K₁ (ws := [⟨scA s sD, (List.replicate (s.gpr .a4).toNat (0 : Byte)).length⟩])
    (by rw [m₁]; exact Proof.RsaPkcs1Sig.frame_writeBytes _ _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr, List.length_replicate]; exact .inl (scSub h (by unfold sD scrBytes; omega)))
  unfold dCopy
  refine WP.seq (wp_mov fun v₁ p₁ f₁ => wp_mov fun v₂ p₂ f₂ => wp_addi (imm := sD) (fun v₃ p₃ f₃ =>
    wp_add fun v₄ p₄ f₄ => wp_sub fun w₂ p₅ f₅ => wp_nil ?_) (by decide))
  have Q : Only [.a4, .a5, .a1] t₁ w₂ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))).mono
  have P₂ := P₁.keep h Q.keep (ws := []) (by rw [Q.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)
  have x4 : w₂.gpr .a4 = s.gpr .a7 := by rw [p₅.get .a4, p₄.get .a4, p₃.get .a4, p₂.get .a4, f₁, P₁.s4]
  have x5 : w₂.gpr .a5 = BitVec.ofNat 64 (stackArg s 0).toNat := by
    rw [p₅.get .a5, p₄.get .a5, p₃.get .a5, f₂, p₁.get .s5, P₁.s5, ← gpr_ofNat]
  have x1 : w₂.gpr .a1 = scA s (sD + (s.gpr .a4).toNat - (stackArg s 0).toNat) := by
    rw [f₅, f₄, f₃, p₂.get .s0, p₁.get .s0, P₁.s0, p₃.get .s1, p₂.get .s1, p₁.get .s1, P₁.s1,
      p₄.get .s5, p₃.get .s5, p₂.get .s5, p₁.get .s5, P₁.s5]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := (stackArg s 13).isLt; have := (s.gpr .a4).isLt; have := (stackArg s 0).isLt
    unfold sD; omega
  have hb₂ : Buf w₂ (stackArg s 0).toNat := fun i hi => by
    rw [x1]
    exact scByte h P₂.wr (a := sD + (s.gpr .a4).toNat - (stackArg s 0).toNat) (n := (stackArg s 0).toNat)
      (by unfold sD scrBytes; omega) i hi
  have hr : ∀ j < (stackArg s 0).toNat, InRegions (w₂.rd ++ w₂.wr) (w₂.gpr .a4 + BitVec.ofNat 64 j) 1 :=
    fun j hj => by
      rw [x4, P₂.rd, h.hrd]
      exact ⟨dR s, List.mem_append_left _ (by simp), Offset.contains_base _ (by omega) (by have := h.wd; omega)⟩
  have hdd : ∀ j < (stackArg s 0).toNat, ∀ i < (stackArg s 0).toNat,
      w₂.gpr .a4 + BitVec.ofNat 64 j ≠ w₂.gpr .a1 + BitVec.ofNat 64 i := fun j hj i hi e => by
    rw [x4, x1, BitVec.add_assoc, BitVec.ofNat_add_ofNat] at e
    have c1 : (dR s).Contains (s.gpr .a7 + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ (by omega) (by have := h.wd; omega)
    have c2 : (sR s).Contains (s.gpr .a7 + BitVec.ofNat 64 j) 1 := by
      rw [e]; exact scContains h (by unfold sD scrBytes; omega)
    exact h.ds _ c1 c2
  refine WP.mono (copyLoop_ok hb₂ (by omega) (acc := []) (n := (stackArg s 0).toNat) h.d1 (by simp) (W_nil w₂)
    rfl x5 hr hdd) fun t ⟨K, m, _⟩ => ?_
  rw [List.nil_append, x1, x4] at m
  have hD : Spec.Rsa.bytesAt w₂.mem (s.gpr .a7) (stackArg s 0).toNat = dBytes s := by
    exact bytes_of_frame (s := s) P₂.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.kd.symm
      · exact h.od.symm
      · exact h.ds) (by have := h.wd; omega)
  rw [hD] at m
  have hl : (dBytes s).length = (stackArg s 0).toNat := bytesAt_length _ _ _
  refine ⟨P₂.keep h K (ws := [⟨scA s (sD + (s.gpr .a4).toNat - (stackArg s 0).toNat), (dBytes s).length⟩])
    (by rw [m]; exact Proof.RsaPkcs1Sig.frame_writeBytes _ _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr, hl]; exact .inl (scSub h (by unfold sD scrBytes; omega))), ?_⟩
  rw [m, Q.mem, m₁, Proof.RsaPkcs1Enc.i2osp_os2ip_pad _ (by rw [hl]; omega)]
  have e : scA s (sD + (s.gpr .a4).toNat - (stackArg s 0).toNat) =
      scA s sD + BitVec.ofNat 64 ((s.gpr .a4).toNat - (dBytes s).length) := by
    rw [hl, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega
  rw [e]
  exact zeros_then _ _ (by rw [hl]; omega) (by omega)

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK initG finG)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

/-- What the proofs know of SHA-256's streaming functions. -/
abbrev hH : HashOK sha256 := VG.Proof.Hmac.Stream.RISCV64.Sha256Family.ok256

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers, and memory outside `ws`. -/
structure After (t : State) (ws : List Region) (w : State) : Prop where
  rd : w.rd = t.rd
  wr : w.wr = t.wr
  sp : w.sp = t.sp
  cs : ∀ r ∈ preserved, w.gpr r = t.gpr r
  frame : Frame ws t.mem w.mem

/-- `[scratch + a, scratch + a + l)`. -/
abbrev scR (s : State) (a l : Nat) : Region := ⟨scA s a, l⟩

/-- The largest stack the callees use, below our frame. -/
def callX : Nat := 2048

theorem hmac_sizes : sha256.ibytes + sha256.F ≤ callX ∧ sha256.fbytes + sha256.F ≤ callX ∧
    sha256.F ≤ callX ∧ sha256.S = 96 ∧ sha256.D = 32 ∧ sha256.B = 64 := by decide

section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte}
include h

omit h in
theorem low_sub {X : Nat} (hX : X ≤ callX) : Region.Sub (below (fb s) X) (lowR s) :=
  below_sub (by unfold callX Impl.Rsa.RISCV64.Priv.frameBytes at *; omega) (by decide)

/-- `Post` is kept by a call writing `scratch` and the callees' frames. -/
theorem Post.after {t w : State} (hp : Post s R EM t) {ws : List Region} (a : After t ws w)
    (hs : ∀ r ∈ ws, Region.Sub r (sR s) ∨ Region.Sub r (lowR s)) : Post s R EM w := by
  have cs := callee_sub s
  have g : ∀ r ∈ kept, w.gpr r = t.gpr r := fun r hr => a.cs r (by revert r; decide)
  refine ⟨hp.toMid.of g a.sp a.rd a.wr (hp.mem.trans (a.frame.sub fun r hr => ?_))
    (hp.sv.frame a.frame fun q hq r hr => ?_), (a.cs _ (by decide)).trans hp.r, ?_⟩
  · rcases hs r hr with hr' | hr'
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), hr'⟩
    · exact ⟨_, List.mem_cons_self .., sub_trans hr' cs⟩
  · have := saved_offs q hq
    rcases hs r hr with hr' | hr'
    · exact (h.ks.sub_left (frame_sub s (by unfold oEnd frameBytes at *; omega))).sub_right hr'
    · exact (slot_low s (by unfold oEnd frameBytes at *; omega)).sub_right hr'
  · rw [← hp.em]
    exact bytes_of_frame (s := t) a.frame (fun r hr => by
      rcases hs r hr with hr' | hr'
      · have := h.os.sub_right hr'; simp only [oR, h.h1] at this; exact this
      · have := (h.ko.symm.sub_right cs).sub_right hr'; simp only [oR, h.h1] at this; exact this)
      (by have := h.wo; have := h.h1; omega)

omit h in
/-- Two parts of `scratch` apart. -/
theorem scDisj {a l b m : Nat} (hab : a + l ≤ b ∨ b + m ≤ a) (ha : a + l ≤ scrBytes) (hb : b + m ≤ scrBytes) :
    Region.Disjoint (scR s a l) (scR s b m) :=
  Offset.disjoint _ hab (by unfold scrBytes at ha; omega) (by unfold scrBytes at hb; omega)

/-- The callees' stack misses `scratch`. -/
theorem lowSc {X a l : Nat} (hX : X ≤ callX) (ha : a + l ≤ scrBytes) :
    (below (fb s) X).Disjoint (scR s a l) :=
  ((h.ks.sub_left (sub_trans (low_sub hX) (callee_sub s))).sub_right (scSub h ha))

/-- The callees' stack is below the stack pointer. -/
theorem fb_ge {X : Nat} (hX : X ≤ callX) : X ≤ (fb s).toNat := by
  have := kb_toNat h; have := fb_toNat h
  unfold stackBytes frameBytes Impl.Rsa.RISCV64.Priv.frameBytes callX at *; omega

/-- Writes of `scratch` and the callees' stack keep `Post`. -/
theorem Post.after_sc {t w : State} (hp : Post s R EM t) {ws : List (Nat × Nat)} {X : Nat} (hX : X ≤ callX)
    (hws : ∀ p ∈ ws, p.1 + p.2 ≤ scrBytes)
    (a : After t (ws.map (fun p => scR s p.1 p.2) ++ [below t.sp X]) w) : Post s R EM w :=
  hp.after h a fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
      exact .inl (scSub h (hws p hp'))
    · rw [List.mem_singleton.mp hr, hp.sp]; exact .inr (low_sub hX)

/-! ## SHA-256 -/

/-- `init` of the state at `scratch + a`. -/
theorem shaInit_ok {t : State} (hp : Post s R EM t) {a : Nat} (ha : a + 96 ≤ scrBytes)
    (h0 : t.gpr .a0 = scA s a) {Q : State → Prop}
    (hQ : ∀ w, Post s R EM w → After t ([scR s a 96] ++ [below t.sp sha256.F]) w →
      hH.SH.Repr w.mem (scA s a) [] → Q w) :
    WP isa sha256.callInit t Q := by
  have hc := scCov h hp.wr ha
  refine hH.callInit_ok h0 (Covers.right hc) hc fun w hrd hwr hsp hf hg hr => ?_
  have A : After t ([scR s a 96] ++ [below t.sp sha256.F]) w := ⟨hrd, hwr, hsp, hg, hf⟩
  exact hQ w (hp.after_sc h (ws := [(a, 96)]) (X := sha256.F) (by decide)
    (by simp only [List.mem_singleton]; rintro _ rfl; exact ha) A) A hr

/-- `update` of the state at `scratch + a` with the `len` bytes at `dat`. -/
theorem shaUpd_ok {t : State} (hp : Post s R EM t) {a : Nat} (ha : a + 96 ≤ scrBytes) {dat : Addr} {len : Nat}
    (h0 : t.gpr .a0 = scA s a) (h2 : t.gpr .a2 = dat) (h3 : (t.gpr .a3).toNat = len)
    (hdc : Covers [⟨dat, len⟩] (t.rd ++ t.wr)) (hd : Region.Disjoint ⟨dat, len⟩ (scR s a 96))
    (hdl : (below (fb s) sha256.F).Disjoint ⟨dat, len⟩) {Q : State → Prop}
    (hQ : ∀ w, Post s R EM w → After t ([scR s a 96] ++ [below t.sp sha256.F]) w →
      (∀ m, hH.SH.Repr t.mem (scA s a) m → t.gpr .a1 = BitVec.ofNat 64 m.length →
        hH.SH.Repr w.mem (scA s a) (m ++ Spec.Sha256.bytesAt t.mem dat len)) → Q w) :
    WP isa sha256.callUpd t Q := by
  have hc := scCov h hp.wr ha
  refine hH.callUpd_ok h0 h2 h3 hd (by rw [hp.sp]; exact fb_al h) (by rw [hp.sp]; exact fb_ge h (by decide))
    (by rw [hp.sp]; exact lowSc h (by decide) ha) (by rw [hp.sp]; exact hdl)
    (Covers.append_left hdc (Covers.right hc)) hc fun w hrd hwr hsp hf hg hr => ?_
  have A : After t ([scR s a 96] ++ [below t.sp sha256.F]) w := ⟨hrd, hwr, hsp, hg, hf⟩
  exact hQ w (hp.after_sc h (ws := [(a, 96)]) (X := sha256.F) (by decide)
    (by simp only [List.mem_singleton]; rintro _ rfl; exact ha) A) A hr

/-- `finalize` of the state at `scratch + a`, into `scratch + o`. -/
theorem shaFin_ok {t : State} (hp : Post s R EM t) {a o : Nat} (ha : a + 96 ≤ scrBytes) (ho : o + 32 ≤ scrBytes)
    (hao : a + 96 ≤ o ∨ o + 32 ≤ a) (h0 : t.gpr .a0 = scA s a) (h2 : t.gpr .a2 = scA s o) {Q : State → Prop}
    (hQ : ∀ w, Post s R EM w → After t ([scR s a 96, scR s o 32] ++ [below t.sp sha256.F]) w →
      (∀ m, hH.SH.Repr t.mem (scA s a) m → m.length < 2 ^ 64 → t.gpr .a1 = BitVec.ofNat 64 m.length →
        Spec.Sha256.bytesAt w.mem (scA s o) 32 = hH.SH.H.hash m) → Q w) :
    WP isa sha256.callFin t Q := by
  have hc := scCov h hp.wr ha
  have hc' := scCov h hp.wr ho
  refine hH.callFin_ok h0 h2 (scDisj (s := s) hao ha ho) (by rw [hp.sp]; exact fb_al h)
    (by rw [hp.sp]; exact fb_ge h (by decide)) (by rw [hp.sp]; exact lowSc h (by decide) ha)
    (by rw [hp.sp]; exact lowSc h (by decide) ho) (Covers.right (Covers.pair hc hc')) (Covers.pair hc hc')
    fun w hrd hwr hsp hf hg hr => ?_
  have A : After t ([scR s a 96, scR s o 32] ++ [below t.sp sha256.F]) w := ⟨hrd, hwr, hsp, hg, hf⟩
  exact hQ w (hp.after_sc h (ws := [(a, 96), (o, 32)]) (X := sha256.F) (by decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> with_reducible assumption) A) A hr

/-! ## HMAC-SHA-256 -/

omit h in
theorem hi_sdepth : sdepth sha256.init ≤ sha256.ibytes + sha256.F := by
  have := hH.initSd; have := hH.updSd; have := hH.finSd
  simp only [Hash.init, Hash.initMain, Hash.longKey, Hash.padKey, Hash.updBlock, Hash.callInit, Hash.callUpd,
    Hash.callFin, Hash.keyLoop, Hash.padLoop, sdepth, Instr.frameBytes]
  omega

omit h in
theorem hf_sdepth : sdepth sha256.finalize ≤ sha256.fbytes + sha256.F := by
  have := hH.updSd; have := hH.finSd
  simp only [Hash.finalize, Hash.finalizeMain, Hash.callUpd, Hash.callFin, sdepth, Instr.frameBytes]
  omega

/-- HMAC's `init` of the inner state at `scratch + i` and the outer one at
`scratch + u`, with the 32-byte key at `scratch + k`. -/
theorem macInit_ok {t : State} (hp : Post s R EM t) {i u k : Nat} (hi : i + 96 ≤ scrBytes)
    (hu : u + 96 ≤ scrBytes) (hk : k + 32 ≤ scrBytes) (hiu : i + 96 ≤ u ∨ u + 96 ≤ i)
    (hki : k + 32 ≤ i ∨ i + 96 ≤ k) (hku : k + 32 ≤ u ∨ u + 96 ≤ k)
    (h0 : t.gpr .a0 = scA s i) (h1 : t.gpr .a1 = scA s u) (h2 : t.gpr .a2 = scA s k)
    (h3 : t.gpr .a3 = BitVec.ofNat 64 32) {Q : State → Prop}
    (hQ : ∀ w, Post s R EM w →
      After t ([scR s i 96, scR s u 96] ++ [below t.sp (sha256.ibytes + sha256.F)]) w →
      hH.SH.Repr w.mem (scA s i) (xorPad (blockKey hH.SH.H (Spec.Sha256.bytesAt t.mem (scA s k) 32)) ipad) →
      hH.SH.Repr w.mem (scA s u) (xorPad (blockKey hH.SH.H (Spec.Sha256.bytesAt t.mem (scA s k) 32)) opad) →
      Q w) :
    WP isa macInitCall t Q := by
  have hl := VG.Proof.Hmac.Stream.RISCV64.HashOK.lay hH
  have zz := hmac_sizes
  have ci := scCov h hp.wr hi
  have cu := scCov h hp.wr hu
  have ck := scCov h hp.wr hk
  have c0 : t.callEntry.gpr .a0 = scA s i := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : t.callEntry.gpr .a1 = scA s u := (State.callEntry_gpr _ (by decide)).trans h1
  have c2 : t.callEntry.gpr .a2 = scA s k := (State.callEntry_gpr _ (by decide)).trans h2
  have c3 : (t.callEntry.gpr .a3).toNat = 32 := by rw [State.callEntry_gpr _ (by decide), h3]; rfl
  have X : sha256.ibytes + sha256.F ≤ callX := zz.1
  refine WP.callAny (k := initG hH.SH (sha256.ibytes + sha256.F))
    (fun _ hs => VG.Proof.Hmac.Stream.RISCV64.Init.correct hH hs) (rd := [scR s k 32])
    (wr := [scR s i 96, scR s u 96]) ?_ (Covers.append_left (Covers.right ck) (Covers.right (Covers.pair ci cu)))
    (Covers.pair ci cu) ?_ (Nat.lt_of_le_of_lt hi_sdepth (Nat.lt_of_le_of_lt X (by decide)))
  · simp only [initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c0, c1, c2, c3, hp.sp]
    exact ⟨trivial, rfl, scDisj (s := s) hiu hi hu, scDisj (s := s) hki hk hi, scDisj (s := s) hku hk hu, fb_al h, fb_ge h X,
      lowSc h X hi, lowSc h X hu, lowSc h X hk⟩
  · intro w hrd hwr hsp hf hcs hpost
    simp only [initG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3]
      at hpost
    have A : After t ([scR s i 96, scR s u 96] ++ [below t.sp (sha256.ibytes + sha256.F)]) w :=
      ⟨hrd, hwr, hsp, hcs, Frame.below_mono hf hi_sdepth (Nat.lt_of_le_of_lt X (by decide))⟩
    exact hQ w (hp.after_sc h (ws := [(i, 96), (u, 96)]) X
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> with_reducible assumption) A)
      A hpost.1 hpost.2

/-- HMAC's `finalize` of the inner state at `scratch + i` and the outer one at
`scratch + u`, with the count in `a2`, into `scratch + o`. -/
theorem macFin_ok {t : State} (hp : Post s R EM t) {i u o : Nat} (hi : i + 96 ≤ scrBytes)
    (hu : u + 96 ≤ scrBytes) (ho : o + 32 ≤ scrBytes) (hiu : i + 96 ≤ u ∨ u + 96 ≤ i)
    (hio : i + 96 ≤ o ∨ o + 32 ≤ i) (huo : u + 96 ≤ o ∨ o + 32 ≤ u)
    (h0 : t.gpr .a0 = scA s i) (h1 : t.gpr .a1 = scA s u) (h3 : t.gpr .a3 = scA s o) {Q : State → Prop}
    (hQ : ∀ w, Post s R EM w →
      After t ([scR s i 96, scR s o 32] ++ [below t.sp (sha256.fbytes + sha256.F)]) w →
      (∀ k0 text, k0.length = 64 → k0.length + text.length < 2 ^ 64 →
        hH.SH.Repr t.mem (scA s i) (xorPad k0 ipad ++ text) →
        t.gpr .a2 = BitVec.ofNat 64 (64 + text.length) →
        hH.SH.Repr t.mem (scA s u) (xorPad k0 opad) →
        Spec.Sha256.bytesAt w.mem (scA s o) 32 = hmacBlockKey hH.SH.H k0 text) → Q w) :
    WP isa macFinCall t Q := by
  have zz := hmac_sizes
  have ci := scCov h hp.wr hi
  have cu := scCov h hp.wr hu
  have co := scCov h hp.wr ho
  have c0 : t.callEntry.gpr .a0 = scA s i := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : t.callEntry.gpr .a1 = scA s u := (State.callEntry_gpr _ (by decide)).trans h1
  have c2 : t.callEntry.gpr .a2 = t.gpr .a2 := State.callEntry_gpr _ (by decide)
  have c3 : t.callEntry.gpr .a3 = scA s o := (State.callEntry_gpr _ (by decide)).trans h3
  have X : sha256.fbytes + sha256.F ≤ callX := zz.2.1
  refine WP.callAny (k := finG hH.SH (sha256.fbytes + sha256.F))
    (fun _ hs => VG.Proof.Hmac.Stream.RISCV64.Finalize.correct hH hs) (rd := [scR s u 96])
    (wr := [scR s i 96, scR s o 32]) ?_ (Covers.append_left (Covers.right cu) (Covers.right (Covers.pair ci co)))
    (Covers.pair ci co) ?_ (Nat.lt_of_le_of_lt hf_sdepth (Nat.lt_of_le_of_lt X (by decide)))
  · simp only [finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c0, c1, c3, hp.sp]
    exact ⟨rfl, rfl, scDisj (s := s) hiu hi hu, scDisj (s := s) hio hi ho, scDisj (s := s) huo hu ho, fb_al h, fb_ge h X,
      lowSc h X hi, lowSc h X hu, lowSc h X ho⟩
  · intro w hrd hwr hsp hf hcs hpost
    simp only [finG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3]
      at hpost
    have A : After t ([scR s i 96, scR s o 32] ++ [below t.sp (sha256.fbytes + sha256.F)]) w :=
      ⟨hrd, hwr, hsp, hcs, Frame.below_mono hf hf_sdepth (Nat.lt_of_le_of_lt X (by decide))⟩
    exact hQ w (hp.after_sc h (ws := [(i, 96), (o, 32)]) X
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> with_reducible assumption) A)
      A hpost

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
