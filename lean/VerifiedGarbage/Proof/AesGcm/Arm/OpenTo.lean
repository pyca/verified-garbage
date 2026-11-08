module

public import VerifiedGarbage.Proof.AesGcm.Arm.Open
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Zeroize.Common
import VerifiedGarbage.Proof.AesGcm.Arm.CTOpen
import VerifiedGarbage.Proof.AesGcm.Arm.CTFn
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesGcm.Arm.Verified
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Copy
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
meta import VerifiedGarbage.Proof.AesGcm.Arm.CTOpen
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Exec

/-!
# AES-GCM decryption out of place on ARMv7: `vg_aes_gcm_open_to`

Untrusted: everything here is checked by Lean. `open_to` is `open`'s body
(`Impl.AesGcm.Arm.openG true`, `openBody_wp`, `openBody_rel`) with the
ciphertext read from `src` and the plaintext written to `dst` in the same
pass (`oneCryptG true`), and the `len` bytes at `dst` zeroed if the tag is
wrong (`openEnd true`, `openTo_wp`). It is constant time for what its
contract makes public, whether the tag is right (`openTo_ct`), and runs in
a frame that allocates its working space on the stack (`openTo_framed`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)

/-! ## The contract -/

/-- What `vg_aes_gcm_open_to` needs: `(ctx = r0, rounds = r1, nonce = r2,
nonce_len = r3, aad = [sp], aad_len = [sp + 4], src = [sp + 8],
len = [sp + 12], dst = [sp + 16], dst_len = [sp + 20], tag = [sp + 24],
tag_len = [sp + 28], work = [sp + 32])`, `dst_len` its `len`, and the 12
bytes below `sp` apart from the buffers. -/
def openToPreArm (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (arg s 0), (arg s 1).toNat⟩
  let src : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
  let dst : Region := ⟨State.addr (arg s 4), (arg s 5).toNat⟩
  let tag : Region := ⟨State.addr (arg s 6), (arg s 7).toNat⟩
  let work : Region := ⟨State.addr (arg s 8), 2560⟩
  s.rd = [ctx, nonce, aad, src, tag, args s 9] ∧ s.wr = [dst, work] ∧
    ctx.Disjoint dst ∧ ctx.Disjoint work ∧ nonce.Disjoint dst ∧ nonce.Disjoint work ∧
    aad.Disjoint dst ∧ aad.Disjoint work ∧ src.Disjoint dst ∧ src.Disjoint work ∧ dst.Disjoint tag ∧
    dst.Disjoint work ∧ dst.Disjoint (args s 9) ∧ tag.Disjoint work ∧ work.Disjoint (args s 9) ∧
    (below12 s.sp).Disjoint ctx ∧ (below12 s.sp).Disjoint nonce ∧ (below12 s.sp).Disjoint aad ∧
    (below12 s.sp).Disjoint src ∧ (below12 s.sp).Disjoint dst ∧ (below12 s.sp).Disjoint tag ∧
    (below12 s.sp).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
    (arg s 8).toNat + 2560 ≤ 2 ^ 32 ∧ 12 ≤ s.sp.toNat ∧ s.sp.toNat + 36 ≤ 2 ^ 32 ∧ roundsOk s ∧
    (arg s 5).toNat = (arg s 3).toNat

/-- What `vg_aes_gcm_open_to` promises: the result in `r0`, and the
plaintext, or zeros, at `dst`. -/
def openToPostArm (s s' : State) : Prop :=
  match openResG true s with
  | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr (arg s 4)) (arg s 3).toNat = pt
  | none => s'.gpr .r0 = 0 ∧ bytesAt s'.mem (State.addr (arg s 4)) (arg s 3).toNat = List.replicate (arg s 3).toNat 0

/-- `vg_aes_gcm_open_to`. -/
def openToArm : Contract isa where
  pre := openToPreArm
  post := openToPostArm
  pub s₁ s₂ := onePub 9 s₁ s₂ ∧ (roundsOk s₁ → (openResG true s₁).isSome = (openResG true s₂).isSome)

theorem bel_sub (s : State) : (bel s).Sub (below12 s.sp) :=
  Offset.sub_below (State.addr s.sp) (a := 8) (n := 8) (b := 12) (m := 12) (by decide) (by decide)

theorem openToPreArm.oPre {s : State} (h : openToPreArm s) : OPre true s := by
  sig_split h
  rename_i hrd hwr cd cw nd nw ad aw sd sw dt dw da tw wa bc bn ba bs bd bt bw fc fn fa fs fd ft fw sp12 spf hR
  have e5 := h
  clear h
  have bl : ∀ {r : Region}, (below12 s.sp).Disjoint r → (bel s).Disjoint r := fun h => h.sub_left (bel_sub s)
  rw [e5] at hwr cd nd ad sd dt dw da bd fd
  have wr2 : ∀ {r : Region}, r ∈ s.wr → r = ⟨State.addr (arg s 4), (arg s 3).toNat⟩ ∨
      r = ⟨State.addr (arg s 8), 2560⟩ := fun hr => by
    rw [hwr] at hr; simpa using hr
  have one : onePre 9 8 s := by
    refine ⟨⟨by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp⟩,
      ⟨List.mem_append_left _ (by rw [hrd]; simp), by rw [hwr]; simp, fun r hr => ?_⟩,
      fun hw => ?_, cw, fun hw => ?_, nw, fun hw => ?_, aw, sw, fun hw => ?_, wa, bl bc, bl bn, bl ba, bl bs,
      bl bw, fc, fn, fa, fs, fw, by omega, spf, hR⟩
    · rcases wr2 hr with rfl | rfl
      · exact da.symm
      · exact wa.symm
    · rcases wr2 hw with e | e <;> rw [e]
      · exact cd
      · exact cw
    · rcases wr2 hw with e | e <;> rw [e]
      · exact nd
      · exact nw
    · rcases wr2 hw with e | e <;> rw [e]
      · exact ad
      · exact aw
    · rcases wr2 hw with e | e <;> rw [e]
      · exact da
      · exact wa
  exact ⟨one, by rw [hrd]; simp, tw, bl bt, ft,
    ⟨by rw [hwr]; simp, cd, sd, dw, da, bl bd, fd, sp12, bc, bs, bd, bw⟩⟩

/-! ## Each run -/

/-- `cmp r0, #0`: whether the result is 0. -/
theorem cmpR0_ok (z : State) : WP isa (.block [.cmp .r0 (imm 0)]) z fun t =>
    t.mem = z.mem ∧ (∀ r, t.gpr r = z.gpr r) ∧ t.sp = z.sp ∧ t.z = (z.gpr .r0 == 0) ∧ t.rd = z.rd ∧
      t.wr = z.wr := by
  refine WP.run ⟨_, by arun [], rfl⟩ fun t ht => ?_
  subst ht
  exact ⟨rfl, fun _ => rfl, rfl, by simp only [z_subFlags]; rw [BitVec.sub_zero], rfl, rfl⟩

/-- One step of the wipe: the byte at `D + i` zeroed. -/
theorem zeroStep_ok (t : State) {D : BitVec 32} {i : Nat} (hd : t.gpr .r1 = D + BitVec.ofNat 32 i)
    (h0 : t.gpr .r3 = 0) (w : InRegions t.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ t', runBlock isa [.strb .r3 .r1 0, addI .r1 .r1 1, .subs .r2 .r2 (imm 1)] t = some t' ∧
      t'.mem = t.mem.writeW (State.addr (D + BitVec.ofNat 32 i)) (0 : BitVec 8) ∧
      t'.gpr .r1 = D + BitVec.ofNat 32 (i + 1) ∧ t'.gpr .r2 = t.gpr .r2 - BitVec.ofNat 32 1 ∧
      t'.z = (t.gpr .r2 - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp := by
  refine ⟨_, by arun [hd, add_ofNat_zero, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_subFlags, Proof.AesGcm.Arm.mem_store, h0]; rfl
  · simp [gpr_setReg, hd, Proof.AesGcm.Arm.add32_ofNat_assoc]
  · simp [gpr_setReg]
  · simp [z_setReg, gpr_setReg]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

/-- `wipeLoop`: the `n` bytes at `D` zeroed, from `r1 = D`, `r2 = n` and
`r3 = 0`. -/
theorem wipeLoop_wp (u : State) {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) (hD : D.toNat + n ≤ 2 ^ 32)
    (h₁ : u.gpr .r1 = D) (h₂ : u.gpr .r2 = BitVec.ofNat 32 n) (h₀ : u.gpr .r3 = 0)
    (hw : Covers [⟨State.addr D, n⟩] u.wr) :
    WP isa wipeLoop u fun u' => Proof.Zeroize.Prefix u'.mem (State.addr D) n ∧
      Frame [⟨State.addr D, n⟩] u.mem u'.mem ∧ (∀ r, r ≠ .r1 → r ≠ .r2 → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧
      u'.wr = u.wr ∧ u'.sp = u.sp := by
  unfold wipeLoop
  have cmp : WP isa (.block [.cmp .r2 (imm 0)]) u fun t => t = subFlags u (u.gpr .r2) (BitVec.ofNat 32 0) :=
    WP.run ⟨_, by arun [], rfl⟩ fun _ h => h.symm
  refine WP.seq (WP.mono cmp fun t ht => ?_)
  subst ht
  have tz : (subFlags u (u.gpr .r2) (BitVec.ofNat 32 0)).z = decide (n = 0) := by
    rw [z_subFlags, h₂]; exact Gather.z_ne0 hn
  refine WP.ite (decide (n = 0)) (eval_eq' tz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), Frame.refl _ _, fun r _ _ => rfl, rfl, rfl, rfl⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.loop (M := isa)
      (body := .block [.strb .r3 .r1 0, addI .r1 .r1 1, .subs .r2 .r2 (imm 1)]) (c := .ne)
      (fun (w : Nat) (v : State) => ∃ i, w = n - i ∧ i < n ∧ v.gpr .r1 = D + BitVec.ofNat 32 i ∧
        v.gpr .r2 = BitVec.ofNat 32 (n - i) ∧ (∀ r, r ≠ .r1 → r ≠ .r2 → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧
        v.wr = u.wr ∧ v.sp = u.sp ∧ Frame [⟨State.addr D, n⟩] u.mem v.mem ∧
        Proof.Zeroize.Prefix v.mem (State.addr D) i) ?_ (n - 0) _
      ⟨0, rfl, by omega, by rw [gpr_subFlags, h₁, add_ofNat_zero], by rw [gpr_subFlags, h₂, Nat.sub_zero],
        fun r _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    rintro w v ⟨i, rfl, hi, r1, r2, gv, rdv, wrv, spv, fv, pv⟩
    have aD : State.addr (D + BitVec.ofNat 32 i) = State.addr D + BitVec.ofNat 64 i := addr_add (by omega)
    have hcn : (⟨State.addr D, n⟩ : Region).Contains (State.addr D + BitVec.ofNat 64 i) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    have win : InRegions v.wr (State.addr (D + BitVec.ofNat 32 i)) 1 := by
      rw [wrv, aD]; exact hw _ _ ⟨_, List.mem_singleton_self _, hcn⟩
    obtain ⟨v', run', mem', r1', r2', z', g', rd', wr', sp'⟩ :=
      zeroStep_ok v r1 (by rw [gv _ (by decide) (by decide), h₀]) win
    refine WP.of_runBlock ⟨v', run', ?_⟩
    have f' : Frame [⟨State.addr D, n⟩] u.mem v'.mem := by
      rw [mem', aD]; exact fv.writeW (List.mem_singleton_self _) _ hcn
    have p' : Proof.Zeroize.Prefix v'.mem (State.addr D) (i + 1) := by
      rw [mem', aD]; exact Proof.Zeroize.prefix_writeW (w := 8) pv (by omega)
    have g'' : ∀ r, r ≠ .r1 → r ≠ .r2 → v'.gpr r = u.gpr r := fun r a b => by rw [g' r a b, gv r a b]
    have hz : v'.z = decide (i + 1 = n) := by rw [z', r2, dec32 hi hn, z_dec hi hn]
    have ev : isa.eval .ne v' = some !decide (i + 1 = n) := eval_ne' hz
    by_cases he : i + 1 = n
    · left
      exact ⟨by rw [ev]; simp [he], by rw [← he]; exact p', f', g'', rd'.trans rdv, wr'.trans wrv,
        sp'.trans spv⟩
    · right
      exact ⟨by rw [ev]; simp [he], n - (i + 1), by omega, i + 1, rfl, by omega, r1',
        by rw [r2', r2, dec32 hi hn], g'', rd'.trans rdv, wr'.trans wrv, sp'.trans spv, f', p'⟩

/-- The zeros of `Prefix`, as bytes. -/
theorem bytesAt_zeros {m : Mem} {D : Addr} {n : Nat} (h : Proof.Zeroize.Prefix m D n) :
    bytesAt m D n = List.replicate n 0 := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact h i (by simpa [bytesAt] using h₁)

/-- The result, from what the body promises. -/
theorem OB.r0 {s₀ s : State} (ob : OB true s₀ s) :
    s.gpr .r0 = if (openResG true s₀).isSome then 1 else 0 := by
  have op := ob.post
  unfold OpenPostG at op
  split at op
  · next e => rw [e]; exact op.1
  · next e => rw [e]; exact op.1

/-- After the registers are restored: the stack arguments and the result. -/
structure OE (s₀ s : State) : Prop where
  args : ArgsKeep (oNa true) s₀ s
  r0 : s.gpr .r0 = if (openResG true s₀).isSome then 1 else 0

/-- The end of `open_to` from where the body leaves the state: the
registers restored, and `dst` zeroed if the tag is wrong. -/
theorem openToEnd_wp {s₀ s : State} (ho : OPre true s₀) (ob : OB true s₀ s) :
    WP isa (openEnd true) s fun s' => abiPreserved s₀ s' ∧ openToPostArm s₀ s' := by
  have h' := ho.one
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ (oNa true) ∈ s₀.rd := h'.1.2.2.2
  obtain ⟨dw, -, -, -, -, -, fD, -⟩ := ho.dst
  have r0 := ob.r0
  obtain ⟨⟨k7, he⟩, sv, hk, op⟩ := ob
  refine WP.seq (WP.mono (restore_ok he.r11 fW (covers_left he.perm.w) sv he.sp) fun s₅ hh => ?_)
  obtain ⟨ab, m₅, r0₅, rd₅, wr₅⟩ := hh
  have hk₅ : ArgsKeep (oNa true) s₀ s₅ := hk.of_eq m₅ (ab.2.trans he.sp.symm) rd₅ wr₅
  refine WP.seq (WP.mono (cmpR0_ok s₅) fun t ⟨tm, tg, tsp, tz, trd, twr⟩ => ?_)
  have hkt : ArgsKeep (oNa true) s₀ t := hk₅.of_eq tm tsp trd twr
  have abt : abiPreserved s₀ t := ⟨fun r hr => by rw [tg]; exact ab.1 r hr, tsp.trans ab.2⟩
  unfold OpenPostG at op
  cases e : openResG true s₀ with
  | some pt =>
    rw [e] at op
    refine WP.ite false (eval_eq' (by rw [tz, r0₅, r0, e]; rfl)) (fun h => absurd h (by decide))
      fun _ => WP.block_nil ⟨abt, ?_⟩
    show match openResG true s₀ with | some pt => _ | none => _
    rw [e]
    exact ⟨by rw [tg, r0₅]; exact op.1, by rw [tm, m₅]; exact op.2⟩
  | none =>
    rw [e] at op
    refine WP.ite true (eval_eq' (by rw [tz, r0₅, r0, e]; rfl)) (fun _ => ?_) (fun h => absurd h (by decide))
    unfold wipeDst
    obtain ⟨i4, v4⟩ := hkt.at spf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
    obtain ⟨i3, v3⟩ := hkt.at spf hin 3 (by decide) (show 4 * 3 = 12 from rfl)
    refine WP.seq (WP.run ⟨_, by arun [i4, v4, i3, v3], rfl⟩ fun a ha => ?_)
    subst ha
    have hw : Covers [⟨State.addr (arg s₀ 4), (arg s₀ 3).toNat⟩] (t.wr) := by
      rw [hkt.wr]; exact covers_of_mem dw
    refine WP.mono (wipeLoop_wp _ (arg s₀ 3).isLt fD (by simp [gpr_setReg, v4])
      (by simp [gpr_setReg, v3]) (by simp [gpr_setReg]) hw) fun u ⟨pz, _, gu, _, _, spu⟩ => ?_
    have g : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → u.gpr r = t.gpr r := fun r a b c => by
      rw [gu r a b]; simp [gpr_setReg, a, b, c]
    refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · have hn : r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 := by
        revert hr; revert r; decide
      rw [g r hn.1 hn.2.1 hn.2.2]; exact abt.1 r hr
    · rw [spu]; exact abt.2
    · show match openResG true s₀ with | some pt => _ | none => _
      rw [e]
      exact ⟨by rw [g _ (by decide) (by decide) (by decide), tg, r0₅, r0, e]; rfl, bytesAt_zeros pz⟩

theorem openTo_wp {s₀ : State} (h : openToArm.pre s₀) :
    WP isa openTo s₀ fun s' => abiPreserved s₀ s' ∧ openToArm.post s₀ s' :=
  have ho := openToPreArm.oPre h
  openBody_wp ho fun _ ob => openToEnd_wp ho ob

/-! ## Constant time -/

/-- The registers restored. -/
theorem restore_OE {t s : State} (ho : OPre true t) (ob : OB true t s) : WP isa (.block restore) s (OE t) := by
  have fW := ho.one.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have r0 := ob.r0
  obtain ⟨⟨k7, he⟩, sv, hk, -⟩ := ob
  exact WP.mono (restore_ok he.r11 fW (covers_left he.perm.w) sv he.sp) fun s₅ ⟨ab, m₅, r0₅, rd₅, wr₅⟩ =>
    ⟨hk.of_eq m₅ (ab.2.trans he.sp.symm) rd₅ wr₅, by rw [r0₅, r0]⟩

/-- Whether the result is 0, which is public. -/
theorem cmp_OE {t s : State} {b : Bool} (hb : (openResG true t).isSome = b) (h : OE t s) :
    WP isa (.block [.cmp .r0 (imm 0)]) s fun s' => OE t s' ∧ s'.z = !b :=
  WP.mono (cmpR0_ok s) fun s' ⟨tm, tg, tsp, tz, trd, twr⟩ =>
    ⟨⟨h.args.of_eq tm tsp trd twr, by rw [tg]; exact h.r0⟩, by rw [tz, h.r0, hb]; cases b <;> rfl⟩

theorem openTo_rel {s₀ s₀' : State} (h0 : openToArm.pre s₀) (h0' : openToArm.pre s₀') (hq : openToArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') openTo fun _ _ => True := by
  have ho := openToPreArm.oPre h0
  have ho' := openToPreArm.oPre h0'
  have hR : roundsOk s₀ := ho.one.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hres := hq.2 hR
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := id hq.1
  have spf := ho.one.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have e8 : arg s₀' 8 = arg s₀ 8 := (qa 8 (by decide)).symm
  -- the registers restored
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have d1 := rel_wp (F := OB true s₀) (F' := OB true s₀') (G := OE s₀) (G' := OE s₀')
    (RelCT.taint (A := taint) (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.env.choose_spec.r11, h.2.env.choose_spec.r11]; exact e8.symm) hB)
    (fun s ob => restore_OE ho ob) (fun s ob => restore_OE ho' ob)
  -- whether the result is 0
  let b := (openResG true s₀).isSome
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.r0]) (.block [.cmp .r0 (imm 0)]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have d2 := rel_wp (F := OE s₀) (F' := OE s₀') (G := fun s => OE s₀ s ∧ s.z = !b)
    (G' := fun s => OE s₀' s ∧ s.z = !b)
    (RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.r0, h.2.r0, hres]) hC)
    (fun s h => cmp_OE rfl h) (fun s h => cmp_OE hres.symm h)
  -- `dst` zeroed if the tag is wrong
  have d3 : RelCT isa (fun a c => (OE s₀ a ∧ a.z = !b) ∧ (OE s₀' c ∧ c.z = !b))
      (.ite .eq wipeDst (.block [])) fun _ _ => True := by
    refine rel_iteQ (!b) (fun s h => h.2) (fun s h => h.2) (fun _ => ?_)
      (fun _ => RelCT.block_nil fun _ _ _ => trivial)
    obtain ⟨_, hW⟩ : ∃ h, (taint.check (argTaint [] (4 * oNa true)) wipeDst h).isSome = true :=
      ⟨_, by taint_decide⟩
    exact RelCT.taint (A := taint) (argTaint [] (4 * oNa true)) (fun s₁ s₂ h =>
      h.1.1.args.agree h.2.1.args q₀ spf qa (one_hw ho.one) (one_hw ho'.one) (rs := []) (by simp)) hW
  exact openBody_rel ho ho' hq.1 hres (d1.seq (d2.seq d3))

theorem openTo_ct : ConstantTime isa openToArm.pre openToArm.pub openTo :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (openTo_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified`, with the working space an argument -/

/-- `vg_aes_gcm_open_to` with `work: *mut [u64; 320]`. -/
def openToScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slice false .u8 "len"), ("dst", .slice true .u8 "dst_len"),
    ("tag", .slice false .u8 "tag_len"), ("work", .array true .u64 320)]
  ret := some .u32

/-- `Proof.AesGcm.openToRoundsContract`, whatever `work` is. -/
def openToScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _work =>
      Spec.Gcm.openToPre A.ptrBits ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen)
    (post := fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _work =>
      Proof.AesGcm.openToRoundsPost A.ptrBits ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _work =>
      Spec.Gcm.openToLeak A.ptrBits ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen)

/-- A state satisfying `vg_aes_gcm_open_to`'s precondition (with no nonce,
additional data, source, destination or tag, and `work` at 0). -/
def otSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x8000, 36⟩] [⟨0, 0⟩, ⟨0, 2560⟩]

/-- The postconditions match on `openResult`; the result is the low word of
`r1:r0`; and `open_to`'s public data include its leak, whether it succeeds
(for `rounds` of 10, 12 or 14). -/
theorem openTo_verified : Verified Arm.target openTo (openToScratchContract Arm.abi 12) :=
  Verified.of_correct (fun _ hs => openTo_wp hs) openTo_ct
    { pre := by
        sig_implies_pre [openToScratchContract, openToScratchSig, Spec.Gcm.openToPre, openToArm,
          openToPreArm, onePub, below12, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
          Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [openToScratchContract, openToScratchSig, Proof.AesGcm.openToRoundsPost, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [openToArm, openToPostArm, openResG, oLi, oTi, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro _
        rw [e]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [openToScratchContract, openToScratchSig, Spec.Gcm.openToLeak, openToArm,
          openToPreArm, onePub, below12, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
          Arm.Loc.val, Arm.State.addr] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
        refine ⟨⟨hsp, h0, h1, h2, h3, fun i hi => ?_⟩, fun hr => leak_bool ?_⟩
        · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega) with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          exacts [a0, a1, a2, a3, a4, a5, a6, a7, a8]
        · have e₁ : ¬((s₁.gpr .r1).toNat = 10 ∨ (s₁.gpr .r1).toNat = 12 ∨ (s₁.gpr .r1).toNat = 14) ↔ False :=
            ⟨fun x => x hr, False.elim⟩
          have e₂ : ¬((s₂.gpr .r1).toNat = 10 ∨ (s₂.gpr .r1).toNat = 12 ∨ (s₂.gpr .r1).toNat = 14) ↔ False :=
            ⟨fun x => x (h1 ▸ hr), False.elim⟩
          simp only [e₁, e₂, ↓reduceIte] at hl
          exact hl
      sat := by
        sig_implies_sat [openToScratchContract, openToScratchSig, Spec.Gcm.openToPre, openToArm,
          openToPreArm, onePub, below12, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
          Arm.Loc.val, Arm.State.addr]
          [otSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using otSat }

/-! ## The working space on the stack -/

section
variable (pb : Nat)

/-- The twelve arguments, one by one. -/
theorem twelve {α : Type} {vs : List α} (h : vs.length = 12) :
    ∃ a b c d e f g i j k l o, vs = [a, b, c, d, e, f, g, i, j, k, l, o] := by
  match vs, h with
  | [a, b, c, d, e, f, g, i, j, k, l, o], _ => exact ⟨a, b, c, d, e, f, g, i, j, k, l, o, rfl⟩

theorem openToSig_length : (Spec.Gcm.openToSig.words pb).length = 12 := rfl

theorem openToPre_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.openToSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToPre pb) vs m₁ →
      Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := twelve (hlen.trans (openToSig_length pb))
  exact h

theorem openToPost_local : ∀ vs m₁ m₂ m' r, vs.length = (Spec.Gcm.openToSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Proof.AesGcm.openToRoundsPost pb) vs m₁ m' r →
      Curry.apply (Spec.Gcm.openToSig.words pb) (Proof.AesGcm.openToRoundsPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, rd, nonce, nl, aad, al, src, len, dst, dl, tag, tl, rfl⟩ :=
    twelve (hlen.trans (openToSig_length pb))
  simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.AesGcm.openToRoundsPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.AesGcm.openToRoundsPost pb) _ m₂ m' r
  dsimp only [Curry.apply, Proof.AesGcm.openToRoundsPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  rw [openResult_local (pb := pb) (le15 hr) (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1)
    (agree_of hb.2.2.2.1) (agree_of hb.2.2.2.2.2)]
  exact h hr

theorem openToLeak_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.openToSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToLeak pb) vs m₁ =
      Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToLeak pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨ctx, rd, nonce, nl, aad, al, src, len, dst, dl, tag, tl, rfl⟩ :=
    twelve (hlen.trans (openToSig_length pb))
  simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Spec.Gcm.openToLeak pb) _ m₁ =
    Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
      (Spec.Gcm.openToLeak pb) _ m₂
  dsimp only [Curry.apply, Spec.Gcm.openToLeak, ArgWord.ofRaw, IntTy.bits]
  by_cases hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨ (rd.setWidth pb).toNat = 14
  · simp only [hr, not_true_eq_false, ↓reduceIte]
    simp only [openResult_local (pb := pb) (le15 hr) (agree_of hb.1) (agree_of hb.2.1)
      (agree_of hb.2.2.1) (agree_of hb.2.2.2.1) (agree_of hb.2.2.2.2.2)]
    rfl
  · simp only [hr, not_false_eq_true, ↓reduceIte]

end

/-- A state satisfying `vg_aes_gcm_open_to`'s precondition, without the
working space. -/
def openToFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x8000, 32⟩] [⟨0, 0⟩]

theorem openToFrameSat_pre : ∃ s, (Proof.AesGcm.openToRoundsContract Arm.abi 2620).pre s := by
  implies_sat [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre,
    Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr]
    [openToFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openToFrameSat

/-- `open_to` in a frame of 2608 bytes (an immediate `sub` can encode) holding its working space and copies
of its eight words of stack arguments. -/
theorem openTo_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2608 8 openTo)
      (Proof.AesGcm.openToRoundsContract Arm.abi 2620) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.openToSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openToPre Arm.abi.ptrBits)
    (post := Proof.AesGcm.openToRoundsPost Arm.abi.ptrBits) (wa := true) (stack := 12)
    (leak := some (Spec.Gcm.openToLeak Arm.abi.ptrBits))
    (m := 8) openTo_verified (by decide) (by decide) (by decide) (by decide)
    (openToPre_local _) (openToPost_local _) openToFrameSat_pre
    (hleak := openToLeak_local _)

end VG.Proof.AesGcm.Arm
