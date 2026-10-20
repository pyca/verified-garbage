module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecBase
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.PrivCall
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Rsa.Arm.PrivVerified
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-OAEP decryption on ARMv7: the call of `vg_rsa_private_checked`

`scratch` to its slot (`start_vp`); the call's arguments (`pa_vp`): `EM`'s
place (at `oEm`) as its output, `n`, `e`, the ciphertext as its input, the
private key, and the rest of `scratch` from `oRsa` on; the call (`call_vp`),
correct and constant time, which writes `EM` (`V`) or zeros and returns
`rV`; then the result to its slot and the flags of `k < 2 hLen + 2`
(`chk_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg copyArg)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In P σ ∧ P.lay.St σ s

/-- The buffers the body only reads, in the run from `σ`. -/
abbrev pB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.p) P.pl
abbrev qB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.q) P.ql
abbrev dpB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dp) P.pl
abbrev dqB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dq) P.ql
abbrev qiB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.qinv) P.pl
abbrev labB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.lab) P.ll
abbrev ctB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.ct) P.K

/-- The private-key operation's outcome. -/
abbrev oc (P : EP) (σ : State) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked P.nB P.eB (ctB P σ) (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ)

/-- What it writes to `EM`'s place, and returns. -/
def emL (K : Nat) : Spec.Rsa.Outcome → List Byte
  | .ok y => y
  | _ => List.replicate K 0

def rOf : Spec.Rsa.Outcome → BitVec 32
  | .ok _ => 1
  | .invalid => 0
  | .fault => 2

/-- `EM`, byte by byte, and the result. -/
abbrev V (P : EP) (σ : State) (i : Nat) : Byte := (emL P.K (oc P σ)).getD i 0
abbrev rV (P : EP) (σ : State) : BitVec 32 := rOf (oc P σ)

/-- A result of the operation has `k` bytes. -/
abbrev OcK (P : EP) (σ : State) : Prop := ∀ y, oc P σ = .ok y → y.length = P.K

/-- The result. -/
abbrev Res (H G : Spec.Mgf1.Hash) (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.RsaOaep.writtenDecrypt m (State.addr P.out) (State.addr P.ml) P.K r
    (Spec.RsaOaep.decrypt H G P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (labB P σ) (ctB P σ))

/-- The end of the body. -/
abbrev Fin (H G : Spec.Mgf1.Hash) (P : EP) (σ s : State) : Prop := S P σ s ∧ Res H G P σ s.mem (s.gpr .r0)

/-- The arguments' places are immediates. -/
theorem arg_lt {j : Nat} (hj : j < 23) : arg j < 4096 := by
  unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega

/-- An argument: its place, readable, and its value. -/
theorem argAt {P : EP} {σ s : State} (hi : In P σ) (hs : P.lay.St σ s) {j : Nat} (hj : j < 23) :
    State.addr (P.B + BitVec.ofNat 32 (arg j)) = P.lay.fr (arg j) ∧
    InRegions (s.rd ++ s.wr) (P.lay.fr (arg j)) 4 ∧
    s.mem.readW (P.lay.fr (arg j)) 32 = P.argv.getD j 0 := by
  have hl : j < P.lay.argv.length := by simp only [EP.argv, List.length_cons, List.length_nil]; omega
  exact ⟨hi.ok.addrB (by
      show arg j < frameBytes + 56 + 76; unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega),
    by rw [hs.rd, hs.wr]; exact hi.ok.arg_read hl, hs.arg hl⟩

/-- A slot, written with `r12 = sp`. -/
theorem slotAt {P : EP} {σ : State} (hi : In P σ) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    State.addr (P.B + BitVec.ofNat 32 d) = P.lay.fr d :=
  hi.ok.addrB (by show d < frameBytes + 56 + 76; unfold frameBytes at hd ⊢; omega)

/-! ## `scratch` to its slot -/

/-- After `decStart`. -/
abbrev C0 (P : EP) (σ s : State) : Prop := Ctx P.lay P.scr σ s ∧ In P σ

theorem start_vp (P : EP) : VP (S P) (.block decStart) (C0 P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.2.sp.trans h₂.2.sp.symm) fun σ s ⟨hi, hs⟩ => ?_
  obtain ⟨a21, r21, v21⟩ := argAt hi hs (j := 21) (by decide)
  replace v21 : s.mem.readW (P.lay.fr (arg 21)) 32 = P.scr := v21
  have hw : WP isa (.block decStart) s fun t => t.mem = s.mem.writeW (P.lay.fr sS) P.scr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [decStart, sp0, ld, st, hs.sp, a21, r21, v21, slotAt hi (d := sS) (by decide),
      hs.inFr (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide), arg_lt]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ⟨⟨?_, ?_⟩, hi⟩
  · exact hs.frameW (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide) (by
      rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) rd wr sp
  · rw [m, Mem.readW_writeW_self32]

/-! ## The call's arguments -/

theorem rdArg {L : Lay} (m : Mem) (v : BitVec 32) {d j : Nat} (hd : d + 4 ≤ 64) (hj : j < 23) :
    (m.writeW (L.fr d) v).readW (L.fr (arg j)) 32 = m.readW (L.fr (arg j)) 32 :=
  Lay.readW_fr_other L m v (by unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega) (by
    unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega) (by omega)

theorem rdS {L : Lay} (m : Mem) (v : BitVec 32) {d : Nat} (hd : d + 4 ≤ 64) :
    (m.writeW (L.fr d) v).readW (L.fr sS) 32 = m.readW (L.fr sS) 32 :=
  Lay.readW_fr_other L m v (by unfold sS; omega) (by decide) (by omega)

/-- Words written to the frame from slot `k` on. -/
def wl (L : Lay) : Mem → Nat → List (BitVec 32) → Mem
  | m, _, [] => m
  | m, k, v :: vs => wl L (m.writeW (L.fr (4 * k)) v) (k + 1) vs

theorem wl_nil (L : Lay) (m : Mem) (k : Nat) : wl L m k [] = m := rfl
theorem wl_cons (L : Lay) (m : Mem) (k : Nat) (v : BitVec 32) (vs : List (BitVec 32)) :
    wl L m k (v :: vs) = wl L (m.writeW (L.fr (4 * k)) v) (k + 1) vs := rfl

theorem wl_other (L : Lay) : ∀ (vs : List (BitVec 32)) (m : Mem) (k j : Nat), j < k → k + vs.length ≤ 16 →
    (wl L m k vs).readW (L.fr (4 * j)) 32 = m.readW (L.fr (4 * j)) 32
  | [], _, _, _, _, _ => rfl
  | v :: vs, m, k, j, hj, hl => by
    rw [wl_cons, wl_other L vs _ (k + 1) j (by omega) (by simp at hl; omega),
      Lay.readW_fr_other _ _ _ (by omega) (by omega) (by simp at hl; omega)]

theorem wl_read (L : Lay) : ∀ (vs : List (BitVec 32)) (m : Mem) (k i : Nat), k ≤ i → i < k + vs.length →
    k + vs.length ≤ 16 → (wl L m k vs).readW (L.fr (4 * i)) 32 = vs.getD (i - k) 0
  | [], _, _, _, h₁, h₂, _ => by simp at h₂; omega
  | v :: vs, m, k, i, h₁, h₂, hl => by
    rw [wl_cons]
    simp only [List.length_cons] at h₂ hl
    by_cases e : i = k
    · subst e
      rw [wl_other L vs _ (i + 1) i (by omega) (by omega), Mem.readW_writeW_self32, Nat.sub_self]; rfl
    · rw [wl_read L vs _ (k + 1) i (by omega) (by omega) (by omega), show i - k = (i - (k + 1)) + 1 by omega]; rfl

theorem wl_frame (L : Lay) : ∀ (vs : List (BitVec 32)) (m : Mem) (k : Nat), k + vs.length ≤ 16 →
    Frame [⟨L.fr 0, 64⟩] m (wl L m k vs)
  | [], _, _, _ => Frame.refl _ _
  | v :: vs, m, k, hl => by
    rw [wl_cons]
    simp only [List.length_cons] at hl
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.zero_le _) (by omega) (by omega))).trans (wl_frame L vs _ (k + 1) (by omega))

/-- The call's stack arguments but the first. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  [BitVec.ofNat 32 P.el, P.ct, BitVec.ofNat 32 P.K, P.p, BitVec.ofNat 32 P.pl, P.q,
    BitVec.ofNat 32 P.ql, P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv, BitVec.ofNat 32 P.pl,
    P.scr + BitVec.ofNat 32 oRsa, BitVec.ofNat 32 (P.scl - 1024)]

theorem pa_wp (P : EP) {σ s : State} (hc : Ctx P.lay P.scr σ s) (hi : In P σ) :
    WP isa (.block privArgs) s fun t =>
      t.mem = wl P.lay (s.mem.writeW (State.addr P.B) P.e) 1 (outv P) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = P.scr + BitVec.ofNat 32 oEm ∧
      t.gpr .r1 = BitVec.ofNat 32 P.K ∧ t.gpr .r2 = P.n ∧ t.gpr .r3 = BitVec.ofNat 32 P.K := by
  have hg := hi.geo
  have hs1 : 1024 ≤ P.scl := by
    have := hi.slK; unfold Spec.RsaPss.scratchWords at this; omega
  obtain ⟨a3, r3, v3⟩ := argAt hi hc.st (j := 3) (by decide)
  obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
  obtain ⟨a5, r5, v5⟩ := argAt hi hc.st (j := 5) (by decide)
  obtain ⟨a6, r6, v6⟩ := argAt hi hc.st (j := 6) (by decide)
  obtain ⟨a7, r7, v7⟩ := argAt hi hc.st (j := 7) (by decide)
  obtain ⟨a8, r8, v8⟩ := argAt hi hc.st (j := 8) (by decide)
  obtain ⟨a9, r9, v9⟩ := argAt hi hc.st (j := 9) (by decide)
  obtain ⟨a10, r10, v10⟩ := argAt hi hc.st (j := 10) (by decide)
  obtain ⟨a11, r11, v11⟩ := argAt hi hc.st (j := 11) (by decide)
  obtain ⟨a13, r13, v13⟩ := argAt hi hc.st (j := 13) (by decide)
  obtain ⟨a15, r15, v15⟩ := argAt hi hc.st (j := 15) (by decide)
  obtain ⟨a19, r19, v19⟩ := argAt hi hc.st (j := 19) (by decide)
  obtain ⟨a22, r22, v22⟩ := argAt hi hc.st (j := 22) (by decide)
  replace v3 : s.mem.readW (P.lay.fr (arg 3)) 32 = P.n := v3
  replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
  replace v5 : s.mem.readW (P.lay.fr (arg 5)) 32 = P.e := v5
  replace v6 : s.mem.readW (P.lay.fr (arg 6)) 32 = BitVec.ofNat 32 P.el := v6
  replace v7 : s.mem.readW (P.lay.fr (arg 7)) 32 = P.p := v7
  replace v8 : s.mem.readW (P.lay.fr (arg 8)) 32 = BitVec.ofNat 32 P.pl := v8
  replace v9 : s.mem.readW (P.lay.fr (arg 9)) 32 = P.q := v9
  replace v10 : s.mem.readW (P.lay.fr (arg 10)) 32 = BitVec.ofNat 32 P.ql := v10
  replace v11 : s.mem.readW (P.lay.fr (arg 11)) 32 = P.dp := v11
  replace v13 : s.mem.readW (P.lay.fr (arg 13)) 32 = P.dq := v13
  replace v15 : s.mem.readW (P.lay.fr (arg 15)) 32 = P.qinv := v15
  replace v19 : s.mem.readW (P.lay.fr (arg 19)) 32 = P.ct := v19
  replace v22 : s.mem.readW (P.lay.fr (arg 22)) 32 = BitVec.ofNat 32 P.scl := v22
  have wF : ∀ d, d + 4 ≤ frameBytes → InRegions s.wr (P.lay.fr d) 4 := fun d hd => hc.st.inFr hd
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  have w0 : InRegions s.wr (State.addr P.B) 4 := by rw [q0]; exact wF 0 (by decide)
  have rdA0 : ∀ (m : Mem) (v : BitVec 32) (j : Nat), j < 23 →
      (m.writeW (State.addr P.B) v).readW (P.lay.fr (arg j)) 32 = m.readW (P.lay.fr (arg j)) 32 :=
    fun m v j hj => by rw [q0]; exact rdArg m v (by decide) hj
  have rdS0 : ∀ (m : Mem) (v : BitVec 32),
      (m.writeW (State.addr P.B) v).readW (P.lay.fr sS) 32 = m.readW (P.lay.fr sS) 32 :=
    fun m v => by rw [q0]; exact rdS m v (by decide)
  prun [privArgs, copyArg, atS, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, wF, hc.slotS, arg_lt,
    a3, r3, v3, a4, r4, v4, a5, r5, v5, a6, r6, v6, a7, r7, v7, a8, r8, v8, a9, r9, v9,
    a10, r10, v10, a11, r11, v11, a13, r13, v13, a15, r15, v15, a19, r19, v19, a22, r22, v22, rdArg, rdS, w0, rdA0,
    rdS0, movw_val (show oEm < 2 ^ 16 by decide), movw_val (show oRsa < 2 ^ 16 by decide),
    movw_val (show 1024 < 2 ^ 16 by decide), Offset.ofNat_sub_ofNat (w := 32) hs1, Nat.reduceMul, wl_cons, wl_nil,
    Nat.reduceAdd]

/-- Before the call. -/
abbrev R1 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ In P σ ∧
    PrivArgs s (P.scr + BitVec.ofNat 32 oEm) P.n P.e P.ct P.p P.q P.dp P.dq P.qinv (P.scr + BitVec.ofNat 32 oRsa)
      P.K P.el P.pl P.ql (P.scl - 1024)

theorem pa_vp (P : EP) : VP (C0 P) (.block privArgs) (R1 P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi⟩ => ?_
  have hg := hi.geo
  refine WP.mono (pa_wp P hc hi) fun t ⟨m, rd, wr, sp, t0, t1, t2, t3⟩ => ?_
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  rw [q0] at m
  have fr : Frame [⟨P.lay.fr 0, 64⟩] s.mem t.mem := by
    rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl 0) (by decide)
      (by decide))).trans (wl_frame _ _ _ 1 (by simp))
  have rd0 : ∀ i, i < 16 → stackArg t i = t.mem.readW (P.lay.fr (4 * i)) 32 := by
    intro i hi
    simp only [stackArg, stackArgAddr, sp, hc.st.sp]
    rw [hc.aFr hg (4 * i) (by unfold frameBytes; omega)]
  have v0 : stackArg t 0 = P.e := by
    rw [rd0 0 (by decide), m, wl_other _ _ _ 1 0 (by decide) (by simp), Mem.readW_writeW_self32]
  have v : ∀ i, 1 ≤ i → i < 16 → stackArg t i = (outv P).getD (i - 1) 0 := fun i h1 h2 => by
    rw [rd0 i h2, m, wl_read _ _ _ 1 i h1 (by simp; omega) (by simp)]
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hi, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨P.lay.FR, List.mem_cons_self, Offset.sub_base _ (show 0 + 64 ≤ frameBytes by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact Lay.fr_sep (by decide) (by decide) (by decide)
  have hs := hi.slK
  unfold Spec.RsaPss.scratchWords at hs
  exact ⟨t0, t1, t2, t3, v0, v 1 (by decide) (by decide), v 2 (by decide) (by decide), v 3 (by decide) (by decide),
    v 4 (by decide) (by decide), v 5 (by decide) (by decide), v 6 (by decide) (by decide), v 7 (by decide) (by decide),
    v 8 (by decide) (by decide), v 9 (by decide) (by decide), v 10 (by decide) (by decide),
    v 11 (by decide) (by decide), v 12 (by decide) (by decide), v 13 (by decide) (by decide),
    v 14 (by decide) (by decide), v 15 (by decide) (by decide), hi.kv, hi.el1, hi.elK, hi.pl1, hi.plK, hi.ql1, hi.qlK,
    by omega, by have := hi.scl32; omega⟩

/-! ## The call -/

/-- The call's output and working space, in `scratch`. -/
abbrev emR (P : EP) : Region := ⟨State.addr (P.scr + BitVec.ofNat 32 oEm), P.K⟩
abbrev scrR (P : EP) : Region := ⟨State.addr (P.scr + BitVec.ofNat 32 oRsa), (P.scl - 1024) * 8⟩

theorem call_geo {P : EP} {σ : State} (hi : In P σ) :
    State.addr (P.scr + BitVec.ofNat 32 oEm) = State.addr P.scr + BitVec.ofNat 64 oEm ∧
    State.addr (P.scr + BitVec.ofNat 32 oRsa) = State.addr P.scr + BitVec.ofNat 64 oRsa ∧
    Region.Sub (emR P) P.SCR ∧ Region.Sub (scrR P) P.SCR ∧ (emR P).Disjoint (scrR P) ∧
    P.scr.toNat + P.scl * 8 ≤ 2 ^ 32 ∧ 1024 ≤ P.scl ∧ P.K ≤ 1024 := by
  have hf := hi.ok.fits P.SCR (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  have hs := hi.slK
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
  have hK := hi.k1024
  have e1 : State.addr (P.scr + BitVec.ofNat 32 oEm) = State.addr P.scr + BitVec.ofNat 64 oEm :=
    addr_add (by unfold oEm; omega)
  have e2 : State.addr (P.scr + BitVec.ofNat 32 oRsa) = State.addr P.scr + BitVec.ofNat 64 oRsa :=
    addr_add (by unfold oRsa; omega)
  refine ⟨e1, e2, ?_, ?_, ?_, hf, by omega, hK⟩
  · rw [emR, e1]; exact Offset.sub_base _ (by unfold oEm; omega)
  · rw [scrR, e2]; exact Offset.sub_base _ (by unfold oRsa; omega)
  · rw [emR, scrR, e1, e2]; exact Offset.disjoint _ (by unfold oEm oRsa; omega) (by unfold oEm; omega)
      (by unfold oRsa; omega)

theorem call_pre {P : EP} {σ s : State} (hr : R1 P σ s) :
    (Spec.Rsa.privateCheckedContract abi Proof.Rsa.Arm.stackBytes).pre
      (s.callEntry.withRegions (privRd P.B P.n P.e P.ct P.p P.q P.dp P.dq P.qinv P.K P.el P.pl P.ql)
        (privWr (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))) := by
  obtain ⟨hc, hi, pa⟩ := hr
  have ok := hi.ok
  obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo hi
  have fit := ok.fit
  have hB := ok.B56
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  refine priv_pre pa hc.st.sp hB (by simp only [frameBytes] at fit; omega) ?_ dIS ?_ ?_
  · intro w hw r hr
    simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [privRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    have ro : ∀ R ∈ P.lay.ro, ∀ {w : Region}, Region.Sub w P.SCR → w.Disjoint R := fun R hR w hw =>
      (ok.rw_ro (w := P.SCR) (r := R) (by simp) hR).sub_left hw
    have fr : ∀ {w : Region}, Region.Sub w P.SCR → w.Disjoint ⟨State.addr P.B, 64⟩ := fun hw => by
      rw [q0]; exact ((ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := 0) (n := 64)
        (by show 0 + 64 ≤ frameBytes + 56; decide)).symm).sub_left hw
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ro P.N (by simp) sI
    · exact ro P.E (by simp) sI
    · exact ro P.CT (by simp) sI
    · exact ro P.PP (by simp) sI
    · exact ro P.QQ (by simp) sI
    · exact ro P.DP (by simp) sI
    · exact ro P.DQ (by simp) sI
    · exact ro P.QI (by simp) sI
    · exact fr sI
    · exact ro P.N (by simp) sS'
    · exact ro P.E (by simp) sS'
    · exact ro P.CT (by simp) sS'
    · exact ro P.PP (by simp) sS'
    · exact ro P.QQ (by simp) sS'
    · exact ro P.DP (by simp) sS'
    · exact ro P.DQ (by simp) sS'
    · exact ro P.QI (by simp) sS'
    · exact fr sS'
  · intro r hr
    have low : (⟨State.addr P.B - BitVec.ofNat 64 3440, 3440⟩ : Region) = P.lay.LOW := rfl
    rw [low]
    simp only [privRd, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI
    · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS'
    · exact ok.low_buf (R := P.N) (.inl (by simp))
    · exact ok.low_buf (R := P.E) (.inl (by simp))
    · exact ok.low_buf (R := P.CT) (.inl (by simp))
    · exact ok.low_buf (R := P.PP) (.inl (by simp))
    · exact ok.low_buf (R := P.QQ) (.inl (by simp))
    · exact ok.low_buf (R := P.DP) (.inl (by simp))
    · exact ok.low_buf (R := P.DQ) (.inl (by simp))
    · exact ok.low_buf (R := P.QI) (.inl (by simp))
    · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · intro r hr
    simp only [privBufs, List.mem_cons, List.not_mem_nil, or_false] at hr
    have fs := fun {R : Region} (hR : R ∈ P.lay.ro ++ P.lay.rw) => ok.fits R hR
    have hg := hi.geo
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · dsimp only; rw [Proof.X25519.Arm.addr_toNat, hg.scr_lt (by decide)]; unfold oEm; omega
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · dsimp only; rw [Proof.X25519.Arm.addr_toNat, hg.scr_lt (Nat.le_refl _)]; unfold oRsa; omega

theorem nB_at {P : EP} {σ s : State} (hi : In P σ) (hs : P.lay.St σ s) :
    Spec.Rsa.bytesAt s.mem (State.addr P.n) P.K = P.nB := (hs.ro (R := P.N) (by simp)).trans hi.nB

theorem eB_at {P : EP} {σ s : State} (hi : In P σ) (hs : P.lay.St σ s) :
    Spec.Rsa.bytesAt s.mem (State.addr P.e) P.el = P.eB := (hs.ro (R := P.E) (by simp)).trans hi.eB

/-- What the operation writes, byte by byte. -/
theorem em_of {m : Mem} {a : Addr} {K : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (h : Spec.Rsa.writtenOutcome m a K r o) :
    r = rOf o ∧ (∀ i < K, m (a + BitVec.ofNat 64 i) = (emL K o).getD i 0) ∧ ∀ y, o = .ok y → y.length = K := by
  cases o with
  | ok y =>
    obtain ⟨hr, hb⟩ := h
    refine ⟨hr, fun i hi => ?_, fun y' e => ?_⟩
    · rw [emL, ← hb, RsaPkcs1Sig.Arm.bytesAt_getD hi]
    · cases e; rw [← hb, RsaPkcs1Sig.Arm.bytesAt_length]
  | invalid =>
    obtain ⟨hr, hb⟩ := h
    refine ⟨hr, fun i hi => ?_, fun y' e => by cases e⟩
    show _ = (List.replicate K 0).getD i 0
    rw [← hb, RsaPkcs1Sig.Arm.bytesAt_getD hi]
  | fault =>
    obtain ⟨hr, hb⟩ := h
    refine ⟨hr, fun i hi => ?_, fun y' e => by cases e⟩
    show _ = (List.replicate K 0).getD i 0
    rw [← hb, RsaPkcs1Sig.Arm.bytesAt_getD hi]

/-- After the call. -/
abbrev R2 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ In P σ ∧ (∀ i < P.K, s.mem (sa P.scr i) = V P σ i) ∧ s.gpr .r0 = rV P σ ∧ OcK P σ

/-- `EM` and the result: the call. -/
theorem call_vp (P : EP) (v : Proof.Rsa.Arm.CrtImpl) :
    VP (R1 P) (.call (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (R2 P) := by
  refine VP.callF (Proof.Rsa.Arm.code_verified v) (privCode_stack v)
    (privRd P.B P.n P.e P.ct P.p P.q P.dp P.dq P.qinv P.K P.el P.pl P.ql)
    (privWr (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))
    (fun _ _ hr => call_pre hr)
    (fun σ s hr => ?_) (fun σ s hr => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' hr rd wr sp fr _ po => ?_)
  · obtain ⟨hc, hi, -⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo hi
    have q0 : State.addr P.B = P.lay.fr 0 := by simp
    have hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.rd, ok.rd]; exact List.mem_append_left _ hR)
    have inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨State.addr P.scr + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, by rw [hs.wr, ok.wr]; simp, Offset.contains_base _ hon (by omega)⟩
    have wr' : Covers (privWr (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))
        s.wr := by
      rw [privWr, e1, e2]; exact (inS (by unfold oEm; omega)).cons (inS (by unfold oRsa; omega))
    refine ⟨Covers.append_left ((hro P.N (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr'.right, wr'⟩
    refine (hro P.CT (by simp)).cons ((hro P.PP (by simp)).cons ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons
      ((hro P.DQ (by simp)).cons ((hro P.QI (by simp)).cons (Covers.cons ?_ Covers.nil))))))
    rw [q0]; exact (Covers.one (hs.inFr (by show 0 + 64 ≤ frameBytes; decide))).right
  · rw [hr.1.st.sp]; exact hr.2.1.ok.B56
  · exact priv_pub h₁.2.2 h₂.2.2 (by rw [h₁.1.st.sp, h₂.1.st.sp]) (by rw [nB_at h₁.2.1 h₁.1.st,
      nB_at h₂.2.1 h₂.1.st]) (by rw [eB_at h₁.2.1 h₁.1.st, eB_at h₂.2.1 h₂.1.st]) _ _
  · obtain ⟨hc, hi, pa⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    have hg := hi.geo
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo hi
    have low : FrameStack.belowA s.sp Proof.Rsa.Arm.stackBytes = P.lay.LOW := by rw [hs.sp]; exact ok.low_eq
    rw [low] at fr
    have hc' : Ctx P.lay P.scr σ s' := hc.write fr (fun r hr => by
      simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨P.SCR, by simp, sI⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · exact ⟨P.lay.LOW, by simp, fun _ h => h⟩) (fun r hr => by
      simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      have sl : (slotR P.lay sS).Disjoint P.SCR :=
        ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes + 56; decide)
      rcases hr with rfl | rfl | rfl
      · exact sl.sub_right sI
      · exact sl.sub_right sS'
      · exact Lay.fr_low (by decide)) rd wr sp
    have := priv_post pa po
    rw [nB_at hi hs, eB_at hi hs, hs.ro (R := P.CT) (by simp), hs.ro (R := P.PP) (by simp),
      hs.ro (R := P.QQ) (by simp), hs.ro (R := P.DP) (by simp), hs.ro (R := P.DQ) (by simp),
      hs.ro (R := P.QI) (by simp)] at this
    obtain ⟨r0, hb, hl⟩ := em_of this
    refine ⟨hc', hi, fun i hi' => ?_, r0, hl⟩
    have e := hb i hi'
    rw [e1] at e
    refine Eq.trans ?_ e
    simp only [sa, oEm, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.zero_add]

end VG.Proof.RsaOaep.Arm.Dec
