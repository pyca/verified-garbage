module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.RndScan
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.RndCallee
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.EncVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on PPC64LE: accepting

With `PS` full after `i` octets: `tape` is `[i, 0]`, and the arguments of
`vg_rsa_pkcs1_encrypt_precomputed` in registers and at `sp + 96` of the
frame (`prep_ok`, into `Args`); the call by its contract (`call_ok`, into
`AfterCall`), narrowed to the regions it reads and writes (`callRd`,
`callWr`), from its precondition at the entry (`preE_entry`); the status
`2 - r` and the wipe of `PS` (`accTail_ok`, `accept_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Random VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.WriteBytes (writeBytes)
open VG.Impl.RsaPkcs1Sig.PPC64LE (fillLoop)

/-- The callee's stack arguments. -/
def callArg (s : State) : Nat → Addr
  | 0 => pb s
  | 1 => BitVec.ofNat 64 (psLen s)
  | 2 => stackArg s 3
  | 3 => stackArg s 4
  | 4 => stackArg s 5
  | _ => stackArg s 6

/-- The callee's stack arguments in the frame. -/
abbrev caR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, 48⟩

/-- After the call's arguments. -/
structure Args (s : State) (i : Nat) (w : State) : Prop extends Fy s w where
  fr : Frame [kR s, tapeR s] s.mem w.mem
  sv : Spill.Saved (fb s) s.gpr saved w.mem
  ls : w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr
  t0 : w.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 i
  t1 : w.mem.readW (s.gpr .r5 + BitVec.ofNat 64 8) 64 = 0
  c0 : w.mem.readW (fb s + BitVec.ofNat 64 96) 64 = callArg s 0
  c1 : w.mem.readW (fb s + BitVec.ofNat 64 104) 64 = callArg s 1
  c2 : w.mem.readW (fb s + BitVec.ofNat 64 112) 64 = callArg s 2
  c3 : w.mem.readW (fb s + BitVec.ofNat 64 120) 64 = callArg s 3
  c4 : w.mem.readW (fb s + BitVec.ofNat 64 128) 64 = callArg s 4
  c5 : w.mem.readW (fb s + BitVec.ofNat 64 136) 64 = callArg s 5
  buf : Spec.Rsa.bytesAt w.mem (pb s) (psLen s) = kept s i
  g3 : w.gpr .r3 = s.gpr .r3
  g4 : w.gpr .r4 = s.gpr .r7
  g5 : w.gpr .r5 = s.gpr .r6
  g6 : w.gpr .r6 = s.gpr .r7
  g7 : w.gpr .r7 = s.gpr .r8
  g8 : w.gpr .r8 = s.gpr .r9
  g9 : w.gpr .r9 = s.gpr .r10
  g10 : w.gpr .r10 = stackArg s 0
  g12 : w.gpr .r12 = fb s

/-! ## Memory -/

/-- A frame write leaves a tape word. -/
theorem rd_tf {s : State} (hp : RPre s) (m : Mem) {e : Nat} (he : e + 8 ≤ frameBytes) (v : BitVec 64)
    {a : Addr} (ha : (tapeR s).Contains a 8) :
    (m.writeW (fb s + BitVec.ofNat 64 e) v).readW a 64 = m.readW a 64 :=
  Mem.readW_writeW_sep (hp.dKt.symm.sep ha (frame_contains s he)) (by decide)

/-- A frame write leaves another frame word. -/
theorem rd_ff (s : State) (m : Mem) {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (v : BitVec 64) :
    (m.writeW (fb s + BitVec.ofNat 64 e) v).readW (fb s + BitVec.ofNat 64 d) 64 =
      m.readW (fb s + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

/-- The stack arguments are read from memory changed only in the stack and
the tape. -/
theorem arg_read' {s : State} (hp : RPre s) {m : Mem} (hm : Frame [kR s, tapeR s] s.mem m) {j : Nat} (hj : j < 7) :
    m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := by
  rw [← stackArgAddr_fb]
  refine hm.readW (in_argsR hj) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.dKa.symm
  · exact hp.dTa.symm

theorem caR_sub (s : State) : Region.Sub (caR s) (kR s) := frame_sub s (by decide)

theorem fr_cw {s : State} {m : Mem} (h : Frame [kR s, tapeR s] s.mem m) {e : Nat} (he : e + 8 ≤ frameBytes)
    (v : BitVec 64) : Frame [kR s, tapeR s] s.mem (m.writeW (fb s + BitVec.ofNat 64 e) v) :=
  h.writeW (List.mem_cons_self ..) _ (frame_contains s he)

theorem fr_tw {s : State} {m : Mem} (h : Frame [kR s, tapeR s] s.mem m) {a : Addr} (ha : (tapeR s).Contains a 8)
    (v : BitVec 64) : Frame [kR s, tapeR s] s.mem (m.writeW a v) :=
  h.writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ ha

theorem gr_cw {s : State} {m₀ m : Mem} (h : Frame [tapeR s, caR s] m₀ m) {e : Nat} (he₁ : 96 ≤ e) (he : e + 8 ≤ 144)
    (v : BitVec 64) : Frame [tapeR s, caR s] m₀ (m.writeW (fb s + BitVec.ofNat 64 e) v) :=
  h.writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Offset.contains _ he₁ (by omega) (by decide))

theorem gr_tw {s : State} {m₀ m : Mem} (h : Frame [tapeR s, caR s] m₀ m) {a : Addr} (ha : (tapeR s).Contains a 8)
    (v : BitVec 64) : Frame [tapeR s, caR s] m₀ (m.writeW a v) :=
  h.writeW (List.mem_cons_self ..) _ ha

/-! ## The arguments -/

theorem prep_ok {s : State} (hp : RPre s) {M : Mem} (hM : Mm s M) {i : Nat} {u : State} (hI : At s M i u)
    (hf : (kept s i).length = psLen s) :
    WP isa (.block (stackArgs ++ Impl.RsaPkcs1Enc.PPC64LE.Random.regArgs)) u (Args s i) := by
  have hP := hp.ps
  have hk2 := hp.k2
  have hMu : Mm s u.mem := by rw [hI.mem]; exact hM.buf _ (by omega)
  have F0 : Frame [kR s, tapeR s] s.mem u.mem := hMu.fr.mono (by simp)
  have hw := hI.wr
  unfold stackArgs Impl.RsaPkcs1Enc.PPC64LE.Random.regArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_std (a := s.gpr .r5) (by rw [hI.r30, BitVec.add_zero]) (in_tape hp u hw (tape_c0 s))
    fun u₁ m₁ => wp_li (by decide) fun u₂ o₂ e₂ => wp_std (a := s.gpr .r5 + BitVec.ofNat 64 8)
    (by rw [o₂.get .r30, m₁.gpr, hI.r30]) (in_tape hp u₂ (by rw [o₂.wr, m₁.wr, hw]) (tape_c8 s))
    fun u₃ m₃ => wp_addSp fun u₄ o₄ e₄ => ?_
  have sp₄ : u₄.sp = fb s := by rw [o₄.sp, m₃.sp, o₂.sp, m₁.sp, hI.sp]
  have r12 : u₄.gpr .r12 = fb s := by rw [e₄, BitVec.add_zero, m₃.sp, o₂.sp, m₁.sp, hI.sp]
  have wr₄ : u₄.wr = fr s :: s.wr := by rw [o₄.wr, m₃.wr, o₂.wr, m₁.wr, hw]
  have rd₄ : u₄.rd = s.rd := by rw [o₄.rd, m₃.rd, o₂.rd, m₁.rd, hI.rd]
  have k₄ : Keep [.r0, .r12] u u₄ := (m₁.keep.trans (o₂.keep.trans (m₃.keep.trans o₄.keep))).mono
  have mem₄ : u₄.mem = (u.mem.writeW (s.gpr .r5) (BitVec.ofNat 64 i)).writeW (s.gpr .r5 + BitVec.ofNat 64 8)
      (BitVec.ofNat 64 0) := by
    rw [o₄.mem, m₃.mem, e₂, o₂.mem, m₁.mem, hI.r4]
  have fin : ∀ {e : Nat}, e + 8 ≤ frameBytes → 32 ≤ e → ∀ v : State, v.wr = u₄.wr →
      InRegions v.wr (fb s + BitVec.ofNat 64 e) 8 := fun h₁ h₂ v hv => by
    rw [hv, wr₄]; exact in_fr s _ h₂ h₁
  refine wp_std (a := fb s + BitVec.ofNat 64 96) (by rw [r12]) (fin (by decide) (by decide) _ rfl)
    fun u₅ m₅ => wp_std (a := fb s + BitVec.ofNat 64 104) (by rw [m₅.gpr, r12])
    (fin (by decide) (by decide) _ m₅.wr) fun u₆ m₆ => ?_
  have g6 : u₆.gpr = u₄.gpr := by rw [m₆.gpr, m₅.gpr]
  have F6 : Frame [kR s, tapeR s] s.mem u₆.mem := by
    rw [m₆.mem, m₅.mem, mem₄]
    exact fr_cw (fr_cw (fr_tw (fr_tw F0 (tape_c0 s) _) (tape_c8 s) _) (by decide) _) (by decide) _
  refine wp_ld (a := fb s + BitVec.ofNat 64 (arg 3)) (by rw [g6, r12])
    (arg_in' hp (by rw [m₆.rd, m₅.rd, rd₄]) (j := 3) (by decide)) fun u₇ o₇ e₇ => ?_
  rw [arg_read' hp F6 (by decide)] at e₇
  refine wp_std (a := fb s + BitVec.ofNat 64 112) (by rw [o₇.get .r12, g6, r12])
    (fin (by decide) (by decide) _ (by rw [o₇.wr, m₆.wr, m₅.wr])) fun u₈ m₈ => ?_
  have F8 : Frame [kR s, tapeR s] s.mem u₈.mem := by rw [m₈.mem, o₇.mem]; exact fr_cw F6 (by decide) _
  refine wp_ld (a := fb s + BitVec.ofNat 64 (arg 4)) (by rw [m₈.gpr, o₇.get .r12, g6, r12])
    (arg_in' hp (by rw [m₈.rd, o₇.rd, m₆.rd, m₅.rd, rd₄]) (j := 4) (by decide))
    fun u₉ o₉ e₉ => ?_
  rw [arg_read' hp F8 (by decide)] at e₉
  refine wp_std (a := fb s + BitVec.ofNat 64 120) (by rw [o₉.get .r12, m₈.gpr, o₇.get .r12, g6, r12])
    (fin (by decide) (by decide) _ (by rw [o₉.wr, m₈.wr, o₇.wr, m₆.wr, m₅.wr])) fun u₁₀ m₁₀ => ?_
  have F10 : Frame [kR s, tapeR s] s.mem u₁₀.mem := by rw [m₁₀.mem, o₉.mem]; exact fr_cw F8 (by decide) _
  have k₁₀ : Keep [.r0] u₄ u₁₀ := (m₅.keep.trans (m₆.keep.trans (o₇.keep.trans (m₈.keep.trans
    (o₉.keep.trans m₁₀.keep))))).mono
  refine wp_ld (a := fb s + BitVec.ofNat 64 (arg 5)) (by rw [k₁₀.get .r12, r12])
    (arg_in' hp (by rw [k₁₀.rd, rd₄]) (j := 5) (by decide)) fun u₁₁ o₁₁ e₁₁ => ?_
  rw [arg_read' hp F10 (by decide)] at e₁₁
  refine wp_std (a := fb s + BitVec.ofNat 64 128) (by rw [o₁₁.get .r12, k₁₀.get .r12, r12])
    (fin (by decide) (by decide) _ (by rw [o₁₁.wr, k₁₀.wr])) fun u₁₂ m₁₂ => ?_
  have F12 : Frame [kR s, tapeR s] s.mem u₁₂.mem := by rw [m₁₂.mem, o₁₁.mem]; exact fr_cw F10 (by decide) _
  have k₁₂ : Keep [.r0] u₄ u₁₂ := (k₁₀.trans (o₁₁.keep.trans m₁₂.keep)).mono
  refine wp_ld (a := fb s + BitVec.ofNat 64 (arg 6)) (by rw [k₁₂.get .r12, r12])
    (arg_in' hp (by rw [k₁₂.rd, rd₄]) (j := 6) (by decide)) fun u₁₃ o₁₃ e₁₃ => ?_
  rw [arg_read' hp F12 (by decide)] at e₁₃
  refine wp_std (a := fb s + BitVec.ofNat 64 136) (by rw [o₁₃.get .r12, k₁₂.get .r12, r12])
    (fin (by decide) (by decide) _ (by rw [o₁₃.wr, k₁₂.wr])) fun u₁₄ m₁₄ => ?_
  have k₁₄ : Keep [.r0] u₄ u₁₄ := (k₁₂.trans (o₁₃.keep.trans m₁₄.keep)).mono
  have mem₁₄ : u₁₄.mem = ((((((u₄.mem.writeW (fb s + BitVec.ofNat 64 96) (pb s)).writeW
      (fb s + BitVec.ofNat 64 104) (BitVec.ofNat 64 (psLen s))).writeW (fb s + BitVec.ofNat 64 112)
      (stackArg s 3)).writeW (fb s + BitVec.ofNat 64 120) (stackArg s 4)).writeW (fb s + BitVec.ofNat 64 128)
      (stackArg s 5)).writeW (fb s + BitVec.ofNat 64 136) (stackArg s 6)) := by
    rw [m₁₄.mem, o₁₃.mem, m₁₂.mem, o₁₁.mem, m₁₀.mem, o₉.mem, m₈.mem, o₇.mem, m₆.mem, m₅.mem, e₁₃, e₁₁, e₉, e₇,
      m₅.gpr, k₄.get .r28, hI.r28, k₄.get .r7, hI.r7]
  have F14 : Frame [kR s, tapeR s] s.mem u₁₄.mem := by rw [m₁₄.mem, o₁₃.mem]; exact fr_cw F12 (by decide) _
  have G14 : Frame [tapeR s, caR s] u.mem u₁₄.mem := by
    rw [mem₁₄, mem₄]
    exact gr_cw (gr_cw (gr_cw (gr_cw (gr_cw (gr_cw (gr_tw (gr_tw (Frame.refl _ _) (tape_c0 s) _) (tape_c8 s) _)
      (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _)
      (by decide) (by decide) _) (by decide) (by decide) _
  have K : Keep ([.r0, .r12] ++ [.r0]) u u₁₄ := k₄.trans k₁₄
  have gK : ∀ r, r ∉ [Reg.r0, .r12, .r0] → u₁₄.gpr r = u.gpr r := fun r hr => K.gpr r hr
  have h12 : u₁₄.gpr .r12 = fb s := (k₁₄.get .r12).trans r12
  have a0 : u₁₄.mem.readW (fb s + BitVec.ofNat 64 (arg 0)) 64 = stackArg s 0 := arg_read' hp F14 (by decide)
  have i0 : InRegions (u₁₄.rd ++ u₁₄.wr) (fb s + BitVec.ofNat 64 (arg 0)) 8 :=
    arg_in' hp (by rw [k₁₄.rd, rd₄]) (by decide)
  have c0 : arg 0 < 2 ^ 15 := by decide
  have d0 : arg 0 % 4 = 0 := by decide
  have g31 := (gK .r31 (by decide)).trans hI.r31
  have g29 := (gK .r29 (by decide)).trans hI.r29
  have g6 := (gK .r6 (by decide)).trans hI.r6
  have g8 := (gK .r8 (by decide)).trans hI.r8
  have g9 := (gK .r9 (by decide)).trans hI.r9
  have g10 := (gK .r10 (by decide)).trans hI.r10
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]
    (Q := fun w => w.gpr .r3 = s.gpr .r3 ∧ w.gpr .r4 = s.gpr .r7 ∧ w.gpr .r5 = s.gpr .r6 ∧
      w.gpr .r6 = s.gpr .r7 ∧ w.gpr .r7 = s.gpr .r8 ∧ w.gpr .r8 = s.gpr .r9 ∧ w.gpr .r9 = s.gpr .r10 ∧
      w.gpr .r10 = stackArg s 0 ∧ w.mem = u₁₄.mem) ?_ rfl)
    fun w ⟨⟨w3, w4, w5, w6, w7, w8, w9, w10, wm⟩, kw'⟩ => ?_
  · prun [Impl.AesGcm.PPC64LE.mov, BitVec.or_self, c0, d0, i0, a0, h12, g31, g29, g6, g8, g9, g10]
  have kw : Keep [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] u₁₄ w := ⟨kw'.gpr, kw'.rd, kw'.wr, kw'.sp, kw'.lr⟩
  have slK : Region.Sub (slR s) (kR s) := frame_sub s (by decide)
  have slD : ∀ r ∈ [tapeR s, caR s], (slR s).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dKt.sub_left slK
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  have psD : ∀ r ∈ [tapeR s, caR s], (⟨pb s, psLen s⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dKt.sub_left (buf_sub s (by omega))
    · exact Offset.disjoint _ (.inr (by decide)) (by unfold oBuf; omega) (by decide)
  have hb := bytesAt_writeBytes M (pb s) (kept s i) (by omega)
  rw [hf] at hb
  refine ⟨((hI.toFx.fy.keep k₄).keep k₁₄).keep kw, wm ▸ F14,
    wm ▸ hMu.sv.frame G14 fun p hp' r hr => (slD r hr).sub_left (slot_sub s hp'), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, by rw [wm, bytes_frame G14 psD (by omega), hI.mem, hb], w3, w4, w5, w6, w7, w8, w9, w10,
    (kw.get .r12).trans h12⟩
  · rw [wm, G14.readW (Region.contains_self _ _) (fun r hr => (slD r hr).sub_left (lr_sub s)) (by decide)]
    exact hMu.ls
  · rw [wm, mem₁₄, rd_tf hp _ (by decide) _ (tape_c0 s), rd_tf hp _ (by decide) _ (tape_c0 s),
      rd_tf hp _ (by decide) _ (tape_c0 s), rd_tf hp _ (by decide) _ (tape_c0 s),
      rd_tf hp _ (by decide) _ (tape_c0 s), rd_tf hp _ (by decide) _ (tape_c0 s), mem₄, rd_t80,
      Mem.readW_writeW_self64]
  · rw [wm, mem₁₄, rd_tf hp _ (by decide) _ (tape_c8 s), rd_tf hp _ (by decide) _ (tape_c8 s),
      rd_tf hp _ (by decide) _ (tape_c8 s), rd_tf hp _ (by decide) _ (tape_c8 s),
      rd_tf hp _ (by decide) _ (tape_c8 s), rd_tf hp _ (by decide) _ (tape_c8 s), mem₄,
      Mem.readW_writeW_self64]; rfl
  · rw [wm, mem₁₄, rd_ff s _ (.inl (by decide)) (by decide) (by decide), rd_ff s _ (.inl (by decide)) (by decide)
      (by decide), rd_ff s _ (.inl (by decide)) (by decide) (by decide), rd_ff s _ (.inl (by decide)) (by decide)
      (by decide), rd_ff s _ (.inl (by decide)) (by decide) (by decide), Mem.readW_writeW_self64]; rfl
  · rw [wm, mem₁₄, rd_ff s _ (.inl (by decide)) (by decide) (by decide), rd_ff s _ (.inl (by decide)) (by decide)
      (by decide), rd_ff s _ (.inl (by decide)) (by decide) (by decide), rd_ff s _ (.inl (by decide)) (by decide)
      (by decide), Mem.readW_writeW_self64]; rfl
  · rw [wm, mem₁₄, rd_ff s _ (.inl (by decide)) (by decide) (by decide), rd_ff s _ (.inl (by decide)) (by decide)
      (by decide), rd_ff s _ (.inl (by decide)) (by decide) (by decide), Mem.readW_writeW_self64]; rfl
  · rw [wm, mem₁₄, rd_ff s _ (.inl (by decide)) (by decide) (by decide), rd_ff s _ (.inl (by decide)) (by decide)
      (by decide), Mem.readW_writeW_self64]; rfl
  · rw [wm, mem₁₄, rd_ff s _ (.inl (by decide)) (by decide) (by decide), Mem.readW_writeW_self64]; rfl
  · rw [wm, mem₁₄, Mem.readW_writeW_self64]; rfl

/-- What the callee reads: `n`, `e`, `msg`, `PS`, `pre` and its stack
arguments. -/
abbrev callRd (s : State) : List Region := [nR s, eR s, msgR s, ⟨pb s, psLen s⟩, preR s, caR s]

/-- What it writes: `out` and the working space. -/
abbrev callWr (s : State) : List Region := [outR s, scrR s]

/-- The callee's narrowed entry state. -/
abbrev callE (s w : State) : State := w.callEntry.withRegions (callRd s) (callWr s)

theorem callE_gpr (s w : State) {r : Reg} (hr : r ∉ linkRegs := by decide) : (callE s w).gpr r = w.gpr r :=
  State.callEntry_gpr w hr

theorem callE_sp {s w : State} {i : Nat} (A : Args s i w) : (callE s w).sp = fb s := A.sp

/-- The callee's stack base, below the frame. -/
theorem kb_callee (s : State) : fb s - BitVec.ofNat 64 Impl.RsaPkcs1Sig.PPC64LE.frameBytes = kb s := by
  rw [fb_eq, BitVec.add_sub_cancel]

theorem callee_kR {s w : State} {i : Nat} (A : Args s i w) :
    VG.Proof.RsaPkcs1Sig.PPC64LE.kR (callE s w) = ⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ := by
  simp only [VG.Proof.RsaPkcs1Sig.PPC64LE.kR, VG.Proof.RsaPkcs1Sig.PPC64LE.fb, callE_sp A, kb_callee]

theorem callee_sub (s : State) : Region.Sub ⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ (kR s) :=
  Region.sub_prefix (by decide)

theorem fb_kb (s : State) (d : Nat) :
    fb s + BitVec.ofNat 64 d = kb s + BitVec.ofNat 64 (Impl.RsaPkcs1Sig.PPC64LE.frameBytes + d) := by
  rw [fb_eq, Offset.add_add]

theorem enc_sdepth : sdepth Impl.RsaPkcs1Enc.PPC64LE.Precomputed.code = Impl.RsaPkcs1Sig.PPC64LE.frameBytes := by
  decide +kernel

theorem psLen_toNat {s : State} (hp : RPre s) : (BitVec.ofNat 64 (psLen s)).toNat = psLen s := by
  have := hp.ps; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem pb_toNat {s : State} (hp : RPre s) : (pb s).toNat + psLen s ≤ 2 ^ 64 := by
  have hF := fb_toNat hp
  have := hp.ps
  have := hp.sp2
  rw [pb, Offset.toNat_add_ofNat]; unfold oBuf frameBytes at *; omega

theorem callE_arg {s w : State} {i : Nat} (A : Args s i w) :
    stackArg (callE s w) 0 = callArg s 0 ∧ stackArg (callE s w) 1 = callArg s 1 ∧
      stackArg (callE s w) 2 = callArg s 2 ∧ stackArg (callE s w) 3 = callArg s 3 ∧
      stackArg (callE s w) 4 = callArg s 4 ∧ stackArg (callE s w) 5 = callArg s 5 := by
  have e : ∀ j, stackArg (callE s w) j = w.mem.readW (fb s + BitVec.ofNat 64 (32 + 8 * (8 + j))) 64 := fun j => by
    show w.mem.readW (w.sp + _) 64 = _; rw [A.sp]
  exact ⟨(e 0).trans A.c0, (e 1).trans A.c1, (e 2).trans A.c2, (e 3).trans A.c3, (e 4).trans A.c4,
    (e 5).trans A.c5⟩

theorem preE_entry {s w : State} (hp : RPre s) {i : Nat} (A : Args s i w) : Enc.PreE (callE s w) := by
  have hP := hp.ps
  have hF := fb_toNat hp
  have hK := kb_toNat hp
  have hk2 := hp.k2
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := callE_arg A
  have g3 : (callE s w).gpr .r3 = s.gpr .r3 := (callE_gpr s w).trans A.g3
  have g4 : (callE s w).gpr .r4 = s.gpr .r7 := (callE_gpr s w).trans A.g4
  have g5 : (callE s w).gpr .r5 = s.gpr .r6 := (callE_gpr s w).trans A.g5
  have g6 : (callE s w).gpr .r6 = s.gpr .r7 := (callE_gpr s w).trans A.g6
  have g7 : (callE s w).gpr .r7 = s.gpr .r8 := (callE_gpr s w).trans A.g7
  have g8 : (callE s w).gpr .r8 = s.gpr .r9 := (callE_gpr s w).trans A.g8
  have g9 : (callE s w).gpr .r9 = s.gpr .r10 := (callE_gpr s w).trans A.g9
  have g10 : (callE s w).gpr .r10 = stackArg s 0 := (callE_gpr s w).trans A.g10
  have hO : Enc.oR (callE s w) = outR s := by simp only [Enc.oR, g3, g4, outR, hp.hok]
  have hN : Enc.nR (callE s w) = nR s := by simp only [Enc.nR, g5, g6]
  have hE : Enc.eR (callE s w) = eR s := by simp only [Enc.eR, g7, g8]
  have hM : Enc.mR (callE s w) = msgR s := by simp only [Enc.mR, g9, g10]
  have hPS : Enc.psR (callE s w) = ⟨pb s, psLen s⟩ := by simp only [Enc.psR, a0, a1, callArg, psLen_toNat hp]
  have hS : Enc.scR (callE s w) = scrR s := by simp only [Enc.scR, a2, a3, callArg]
  have hQ : Enc.pR (callE s w) = preR s := by simp only [Enc.pR, a4, a5, callArg]
  have hA : Enc.a6R (callE s w) = caR s := by
    simp only [Enc.a6R, caR]; congr 1; show (callE s w).sp + _ = _; rw [callE_sp A]
  have hKR := callee_kR A
  have cs := callee_sub s
  have ps : Region.Sub ⟨pb s, psLen s⟩ (kR s) := buf_sub s (by omega)
  have ca := caR_sub s
  have kps : Region.Disjoint ⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ ⟨pb s, psLen s⟩ := by
    rw [pb, fb_kb]
    exact Offset.base_disjoint _ (by omega) (by unfold rndStack oBuf Impl.RsaPkcs1Sig.PPC64LE.frameBytes at *; omega)
  have ka : Region.Disjoint ⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ (caR s) := by
    rw [caR, fb_kb]
    exact Offset.base_disjoint _ (by omega) (by unfold rndStack Impl.RsaPkcs1Sig.PPC64LE.frameBytes at *; omega)
  exact {
    sp1 := by rw [callE_sp A]; exact hF.2
    sp2 := by rw [callE_sp A]; have := hp.sp2; unfold frameBytes at hF; omega
    hrd := by rw [hN, hE, hM, hPS, hQ, hA]; rfl
    hwr := by rw [hO, hS]; rfl
    on := by rw [hO, hN]; exact hp.dOn
    oe := by rw [hO, hE]; exact hp.dOe
    om := by rw [hO, hM]; exact hp.dOm
    ops := by rw [hO, hPS]; exact hp.dKo.symm.sub_right ps
    osc := by rw [hO, hS]; exact hp.dOs
    op := by rw [hO, hQ]; exact hp.dOq
    oa := by rw [hO, hA]; exact hp.dKo.symm.sub_right ca
    ns := by rw [hN, hS]; exact hp.dNs
    es := by rw [hE, hS]; exact hp.dEs
    ms := by rw [hM, hS]; exact hp.dMs
    pss := by rw [hPS, hS]; exact hp.dKs.sub_left ps
    sp := by rw [hS, hQ]; exact hp.dSq
    sa := by rw [hS, hA]; exact hp.dKs.symm.sub_right ca
    ko := by rw [hKR, hO]; exact hp.dKo.sub_left cs
    kn := by rw [hKR, hN]; exact hp.dKn.sub_left cs
    ke := by rw [hKR, hE]; exact hp.dKe.sub_left cs
    km := by rw [hKR, hM]; exact hp.dKm.sub_left cs
    kps := by rw [hKR, hPS]; exact kps
    ksc := by rw [hKR, hS]; exact hp.dKs.sub_left cs
    kp := by rw [hKR, hQ]; exact hp.dKq.sub_left cs
    ka := by rw [hKR, hA]; exact ka
    wo := by rw [g3, g4]; have := hp.wO; rw [hp.hok] at this; exact this
    wn := by rw [g5, g6]; exact hp.wN
    we := by rw [g7, g8]; exact hp.wE
    wm := by rw [g9, g10]; exact hp.wM
    wps := by rw [a0, a1]; simp only [callArg]; rw [psLen_toNat hp]; exact pb_toNat hp
    wsc := by rw [a2, a3]; exact hp.wS
    wp := by rw [a4, a5]; exact hp.wQ
    k1 := by rw [g6]; exact hp.k1
    k2 := by rw [g6]; exact hp.k2
    ok := by rw [g4, g6]
    e1 := by rw [g8]; exact hp.L1
    e2 := by rw [g8, g6]; exact hp.L2
    ml := by rw [g10, g6]; exact hp.hml
    pl := by rw [a1, g6, g10]; simp only [callArg]; rw [psLen_toNat hp]; rfl
    hs := by rw [g6, a3]; exact hp.hsl
    hp := by rw [g6, a5]; exact hp.hql }

theorem call_covers {s w : State} (hp : RPre s) {i : Nat} (A : Args s i w) :
    Covers (callRd s ++ callWr s) (w.rd ++ w.wr) ∧ Covers (callWr s) w.wr := by
  have hP := hp.ps
  have hw : Covers (callWr s) w.wr := by
    rw [A.wr, hp.hwr]
    exact Covers.of_mem fun r hr => by
      simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, hp.hrd]
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.right (Covers.one (in_fr s _ (by decide) (by unfold oBuf frameBytes; omega)))
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.right (Covers.one (in_fr s _ (by decide) (by decide)))

/-- After the call. -/
structure AfterCall (s : State) (i : Nat) (y : State) : Prop extends Fy s y where
  fr : Frame [kR s, tapeR s, outR s, scrR s] s.mem y.mem
  sv : Spill.Saved (fb s) s.gpr saved y.mem
  ls : y.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr
  t0 : y.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 i
  t1 : y.mem.readW (s.gpr .r5 + BitVec.ofNat 64 8) 64 = 0
  res : Spec.Rsa.publicPrecompute (nB s) = some (preW s) →
    Spec.Rsa.written y.mem (s.gpr .r3) (kOf s) ((y.gpr .r3).setWidth 32)
      (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) (kept s i))

theorem call_ok {s w : State} (hp : RPre s) {i : Nat} (A : Args s i w) :
    WP isa encCall w (AfterCall s i) := by
  have hP := hp.ps
  obtain ⟨hc, hw⟩ := call_covers hp A
  unfold encCall
  refine WP.callAny (k := encK) Enc.code_verified.1 (enc_pre (preE_entry hp A)) hc hw
    (fun y hrd hwr hsp hf hpres hpost => ?_) (by rw [enc_sdepth]; decide)
  have hb : below w.sp (sdepth Impl.RsaPkcs1Enc.PPC64LE.Precomputed.code) =
      ⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ := by
    rw [enc_sdepth, A.sp]
    show (⟨fb s - BitVec.ofNat 64 Impl.RsaPkcs1Sig.PPC64LE.frameBytes, _⟩ : Region) = _
    rw [kb_callee]
  rw [hb] at hf
  simp only [callWr, List.cons_append, List.nil_append] at hf
  have hpr : ∀ r ∈ preserved, y.gpr r = w.gpr r := hpres
  have cs := callee_sub s
  have kd : ∀ {R : Region}, R.Disjoint (outR s) → R.Disjoint (scrR s) →
      R.Disjoint ⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ →
      ∀ r ∈ [outR s, scrR s, (⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ : Region)], R.Disjoint r :=
    fun h₁ h₂ h₃ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h₁, h₂, h₃]
  have slK : Region.Sub (slR s) (kR s) := frame_sub s (by decide)
  have slC : (slR s).Disjoint ⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ := by
    rw [slR, fb_kb]
    exact Offset.disjoint_base _ (by omega) (by unfold Impl.RsaPkcs1Sig.PPC64LE.frameBytes; decide)
  have slD := kd (hp.dKo.sub_left slK) (hp.dKs.sub_left slK) slC
  have tD := kd hp.dOt.symm hp.dTs (hp.dKt.sub_left cs).symm
  refine ⟨⟨hsp.trans A.sp, hrd.trans A.rd, hwr.trans A.wr,
      fun r hr => (hpr r (by revert r; decide)).trans (A.hi r hr), (hpr _ (by decide)).trans A.r28⟩,
    ?_, A.sv.frame hf fun p hp' r hr => (slD r hr).sub_left (slot_sub s hp'), ?_, ?_, ?_, ?_⟩
  · refine (A.fr.mono (by simp)).trans (hf.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨outR s, by simp, fun _ h => h⟩
    · exact ⟨scrR s, by simp, fun _ h => h⟩
    · exact ⟨kR s, by simp, cs⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => (slD r hr).sub_left (lr_sub s)) (by decide)]; exact A.ls
  · rw [hf.readW (tape_c0 s) tD (by decide)]; exact A.t0
  · rw [hf.readW (tape_c8 s) tD (by decide)]; exact A.t1
  · intro hq
    have hpo := enc_post hpost
    obtain ⟨a0, a1, -, -, a4, a5⟩ := callE_arg A
    simp only [State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem, callE_gpr s w (r := .r3),
      callE_gpr s w (r := .r5), callE_gpr s w (r := .r6), callE_gpr s w (r := .r7), callE_gpr s w (r := .r8),
      callE_gpr s w (r := .r9), callE_gpr s w (r := .r10), A.g3, A.g5, A.g6, A.g7, A.g8, A.g9, A.g10, a0, a1,
      a4, a5, callArg, psLen_toNat hp, A.buf] at hpo
    have hn : Spec.Rsa.bytesAt w.mem (s.gpr .r6) (s.gpr .r7).toNat = nB s :=
      bytes_frame A.fr (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [hp.dKn.symm, hp.dTn.symm]) (by have := hp.wN; omega)
    have he : Spec.Rsa.bytesAt w.mem (s.gpr .r8) (s.gpr .r9).toNat = eB s :=
      bytes_frame A.fr (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [hp.dKe.symm, hp.dTe.symm]) (by have := hp.wE; omega)
    have hm : Spec.Rsa.bytesAt w.mem (s.gpr .r10) (stackArg s 0).toNat = msgB s :=
      bytes_frame A.fr (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [hp.dKm.symm, hp.dTm.symm]) (by have := hp.wM; omega)
    have hw' : Spec.Rsa.wordsAt w.mem (stackArg s 5) (stackArg s 6).toNat = preW s :=
      words_frame A.fr fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [hp.dKq.symm, hp.dTq.symm]
    rw [hn, he, hm, hw'] at hpo
    exact hpo hq

/-! ## The status and the wipe -/

/-- `writtenRandom` from `written` and the status `2 - r`. -/
theorem written_random {m : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {res : Option (List Byte)}
    (h : Spec.Rsa.written m out k r res) :
    Spec.RsaPkcs1Enc.writtenRandom m out k (2 - r) res := by
  cases res with
  | some C => obtain ⟨h1, h2⟩ := h; subst h1; exact ⟨rfl, h2⟩
  | none => obtain ⟨h1, h2⟩ := h; subst h1; exact ⟨rfl, h2⟩

theorem trunc_sub2 (a : BitVec 64) : (BitVec.ofNat 64 2 - a).setWidth 32 = 2 - a.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  have h2 : (2 : BitVec 32).toNat = 2 := rfl
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, h2]
  have := a.isLt
  omega

theorem accTail_ok {s y : State} (hp : RPre s) {i : Nat} (A : AfterCall s i y) :
    WP isa (.seq (.block status) (.seq fillLoop (.block [Impl.AesGcm.PPC64LE.mov .r3 .r5]))) y fun x =>
      Saves s x ∧ x.rd = s.rd ∧ x.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 i ∧
      x.mem.readW (s.gpr .r5 + BitVec.ofNat 64 8) 64 = 0 ∧
      (Spec.Rsa.publicPrecompute (nB s) = some (preW s) →
        Spec.RsaPkcs1Enc.writtenRandom x.mem (s.gpr .r3) (kOf s) ((x.gpr .r3).setWidth 32)
          (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) (kept s i))) := by
  have hP := hp.ps
  unfold status
  refine WP.seq (wp_li (by decide) fun y₁ o₁ e₁ => wp_sub fun y₂ o₂ e₂ => wp_addSp fun y₃ o₃ e₃ =>
    wp_addi fun y₄ o₄ e₄ => wp_mov fun y₅ o₅ e₅ => wp_li (by decide) fun z o₆ e₆ => wp_nil ?_)
  have k : Keep [.r5, .r12, .r4, .r11, .r0] y z :=
    (o₁.keep.trans (o₂.keep.trans (o₃.keep.trans (o₄.keep.trans (o₅.keep.trans o₆.keep))))).mono
  have zm : z.mem = y.mem := by rw [o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have z4 : z.gpr .r4 = pb s := by
    rw [o₆.get .r4, o₅.get .r4, e₄, e₃, BitVec.add_zero, o₂.sp, o₁.sp, A.sp]
  have z11 : z.gpr .r11 = BitVec.ofNat 64 (psLen s) := by
    rw [o₆.get .r11, e₅, o₄.get .r28, o₃.get .r28, o₂.get .r28, o₁.get .r28, A.r28]
  have z5 : z.gpr .r5 = BitVec.ofNat 64 2 - y.gpr .r3 := by
    rw [o₆.get .r5, o₅.get .r5, o₄.get .r5, o₃.get .r5, e₂, e₁, o₁.get .r3]
  have zw : z.wr = fr s :: s.wr := k.wr.trans A.wr
  refine WP.seq (WP.mono (fill_ok (n := psLen s) (p := pb s) (b := 0) (by omega) (by omega) z4 z11
    (by rw [e₆]; rfl) (in_ps s z zw (by omega))) fun x₁ ⟨k₁, m₁⟩ => ?_)
  refine wp_mov fun x o₂' e₂' => wp_nil ?_
  have kk : Keep ([.r5, .r12, .r4, .r11, .r0] ++ ([.r4, .r11] ++ [.r3])) y x := k.trans (k₁.trans o₂'.keep)
  have fy : Fy s x := A.toFy.keep kk
  have hf : Frame [⟨pb s, psLen s⟩] y.mem x.mem := by rw [o₂'.mem, m₁, zm]; exact wipe_frame s _ _
  have slD : (slR s).Disjoint ⟨pb s, psLen s⟩ := slR_buf s (by omega)
  have bs := buf_sub s (n := psLen s) (by omega)
  have tD : ∀ r ∈ [(⟨pb s, psLen s⟩ : Region)], (tapeR s).Disjoint r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hp.dKt.sub_left bs).symm
  refine ⟨⟨fy.sp, fy.wr, fy.hi, A.sv.frame hf fun p hp' r hr => by
      rw [List.mem_singleton.mp hr]; exact slD.sub_left (slot_sub s hp'),
    by rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact slD.sub_left (lr_sub s)) (by decide)]; exact A.ls⟩, fy.rd,
    by rw [hf.readW (tape_c0 s) tD (by decide)]; exact A.t0, by rw [hf.readW (tape_c8 s) tD (by decide)]; exact A.t1,
    fun hq => ?_⟩
  have hw := written_random (A.res hq)
  have hx3 : (x.gpr .r3).setWidth 32 = 2 - (y.gpr .r3).setWidth 32 := by
    rw [e₂', k₁.get .r5, z5, trunc_sub2]
  have hout : Spec.Rsa.bytesAt x.mem (s.gpr .r3) (kOf s) = Spec.Rsa.bytesAt y.mem (s.gpr .r3) (kOf s) :=
    bytes_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]
      have e : (⟨s.gpr .r3, kOf s⟩ : Region) = outR s := by simp only [outR, kOf, hp.hok]
      rw [e]; exact hp.dKo.symm.sub_right bs) (by have := hp.k2; unfold kOf; omega)
  rw [hx3]
  cases hres : Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) (kept s i) <;> rw [hres] at hw <;>
    exact ⟨hw.1, hout.trans hw.2⟩

theorem accept_ok {s : State} (hp : RPre s) {M : Mem} (hM : Mm s M) {i : Nat} {u : State} (hI : At s M i u)
    (hf : (kept s i).length = psLen s)
    (hpre : Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s i, i)) :
    WP isa accept u (Fin s) := by
  unfold accept
  refine WP.seq (WP.mono (prep_ok hp hM hI hf) fun w A => WP.seq (WP.mono (call_ok hp A) fun y C => ?_))
  refine WP.mono (accTail_ok hp C) fun x ⟨sv, rd, t0, t1, hr⟩ => ⟨sv, rd, ?_⟩
  obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_accepted hpre
  show (∃ req, _ ∧ _ ∧ _) ∧ _
  unfold Spec.Entropy.Result.Requests
  rw [ho, hu]
  exact ⟨⟨0, t0, t1, rfl⟩, hr⟩

end VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd
