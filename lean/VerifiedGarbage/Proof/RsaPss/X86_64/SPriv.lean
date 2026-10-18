module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SEnc
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecPriv
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS signing on x86-64: the call of `vg_rsa_private_checked`

With its stack arguments in the frame's first 14 words (`EM` at
`scratch + oEm` as the input, the private key, the rest of `scratch`:
`privArgsS_ok`), `vg_rsa_private_checked` runs under its contract
(`privS_pre`), and returns with `out` written as it says (`privS_call`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sScrLen sOut sN sK sE sEl oEm oRsa arg scr)
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Proof.RsaOaep.X86_64 (decStack stkD fb frR frame_subD ret_subD below_subD Lay Rep upd nW StepW outR
  wp_good block_good keep_cs3 cs_disj ea_sp off_plus argAddr stackArgAddr_j stackArg_entry kbD fb_eqD fb_sub8D
  owned_one)
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Proof.RsaPkcs1Enc.X86_64 (privStack privK PrivImpl)

variable {s : State}

/-! ## The stack arguments -/

/-- A stack argument, read from memory changed only where the function writes. -/
theorem arg_readF (hp : SPre s) {m : Mem} (hf : FrS s m) {j : Nat} (hj : j < 20) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := sargsR s) ?_ (fun r' hr' => ?_) (by decide)
  · rw [stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact hp.dKa.symm
    · exact hp.dOa.symm
    · exact hp.dsa.symm

theorem FrS.frame {m m' : Mem} (h : FrS s m) (h' : Frame [frR s] m m') : FrS s m' :=
  h.trans (h'.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_subD s⟩)

theorem frame_wF (hp : SPre s) {m : Mem} {d : Nat} (hd : d + 8 ≤ frameBytes) (v : BitVec 64) :
    Frame [frR s] m (m.writeW (off (fb s) d) v) := frame_wS hp (Frame.refl _ _) hd v

/-- Stack argument `j` (of ours) to word `j + 2` of the frame. -/
def cpyArg (j : Nat) : List Instr := [.mov .rax (.mem (arg j)), .store (sp (16 + 8 * j)) .rax]

def privTail : List Instr :=
  scr .rax oEm ++ ([.store (sp 0) .rax, .mov .rax (.mem (sp sK)), .store (sp 8) .rax] : List Instr) ++
  scr .rax oRsa ++ ([.store (sp 96) .rax, .mov .rax (.mem (sp sScrLen)), .alu .sub .rax (.imm 1024),
    .store (sp 104) .rax] : List Instr) ++
  ([.mov .rdi (.mem (sp sOut)), .mov .rsi (.mem (sp sK)), .mov .rdx (.mem (sp sN)), .mov .rcx (.mem (sp sK)),
    .mov .r8 (.mem (sp sE)), .mov .r9 (.mem (sp sEl))] : List Instr)

theorem privArgs_eq : privArgs = (List.range 10).flatMap cpyArg ++ privTail := rfl

theorem cpyArg_ok (hp : SPre s) {u : State} {S : Addr} (L : Lay u (fb s) S) (hrd : u.rd = s.rd)
    (hf : FrS s u.mem) {j : Nat} (hj : j < 10) :
    WP isa (.block (cpyArg j)) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) (16 + 8 * j)) (stackArg s j) := by
  have hin := hp.arg_in hrd (j := j) (by omega)
  refine WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) (16 + 8 * j)) (stackArg s j)) ?_ rfl
    |> WP.mono <| fun u' ⟨hm, k⟩ => ⟨k, hm⟩
  xrun [cpyArg, arg, ea_sp, L.rsp, hin, arg_readF hp hf (j := j) (by omega),
    L.st (d := 16 + 8 * j) (by unfold frameBytes; omega)]

/-- The words the copies leave. -/
def cpW (s : State) (W : Nat → BitVec 64) (n : Nat) (i : Nat) : BitVec 64 :=
  if 2 ≤ i ∧ i < 2 + n then stackArg s (i - 2) else W i

theorem cpys_ok (hp : SPre s) {S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} :
    ∀ n ≤ 10, ∀ u : State, Lay u (fb s) S → u.rd = s.rd → FrS s u.mem → Rep u.mem (fb s) S V W →
    WP isa (.block ((List.range n).flatMap cpyArg)) u fun u' => Keep [.rax] u u' ∧ Lay u' (fb s) S ∧
      FrS s u'.mem ∧ Frame [frR s] u.mem u'.mem ∧ Rep u'.mem (fb s) S V (cpW s W n)
  | 0, _, u, L, _, hA, R => WP.block_nil ⟨Keep.refl _ _, L, hA, Frame.refl _ _, by
      refine (congrArg (fun W' => Rep u.mem (fb s) S V W') (funext fun i => ?_)).mp R
      simp only [cpW]; rw [ifn (by omega)]⟩
  | n + 1, hn, u, L, hrd, hA, R => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (cpys_ok hp n (by omega) u L hrd hA R) fun u1 ⟨k1, L1, hA1, f1, R1⟩ => ?_
    refine WP.mono (cpyArg_ok hp L1 (k1.2.1.trans hrd) hA1 (j := n) (by omega)) fun u2 ⟨k2, hm2⟩ => ?_
    have R2 := R1.wf L1.geo (k := n + 2) (by unfold nW frameBytes; omega) (stackArg s n)
    rw [show off (fb s) (8 * (n + 2)) = off (fb s) (16 + 8 * n) by congr 1; omega, ← hm2] at R2
    have R2' : Rep u2.mem (fb s) S V (cpW s W (n + 1)) := by
      refine (congrArg (fun W' => Rep u2.mem (fb s) S V W') (funext fun i => ?_)).mp R2
      simp only [upd, cpW]
      by_cases hi : i = n + 2
      · subst hi; rw [ifp rfl, ifp (by omega), show n + 2 - 2 = n by omega]
      · rw [ifn hi]
        by_cases h' : 2 ≤ i ∧ i < 2 + n
        · rw [ifp h', ifp (by omega)]
        · rw [ifn h', ifn (by omega)]
    have f2 : Frame [frR s] u1.mem u2.mem := by
      rw [hm2]; exact frame_wF hp (d := 16 + 8 * n) (by unfold frameBytes; omega) _
    refine ⟨(k1.trans k2).mono (by decide), L1.of_rep' R1 R2'
        (by simp only [cpW]; rw [ifn (by omega), ifn (by omega)]) (k2.gpr (by decide)) k2.2.2,
      hA1.frame f2, f1.trans f2, R2'⟩

theorem off_zero (p : Addr) : off p 0 = p := BitVec.add_zero p

/-- The private-key operation's stack arguments. -/
def pArg (s : State) (i : Nat) : BitVec 64 :=
  match i with
  | 0 => off (stackArg s 14) oEm
  | 1 => s.gpr .rcx
  | 12 => off (stackArg s 14) oRsa
  | 13 => stackArg s 15 - BitVec.ofNat 64 1024
  | i => stackArg s (i - 2)

/-- The private-key operation's arguments: its stack arguments in the
frame's first words, the rest of ours kept, and its registers. -/
theorem privArgsS_ok (hp : SPre s) {u : State} (L : Lay u (fb s) (stackArg s 14)) (hrd : u.rd = s.rd)
    (hA : FrS s u.mem) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 14) V W)
    (h21 : W 21 = s.gpr .rdi) (h23 : W 23 = s.gpr .rcx) (h22 : W 22 = s.gpr .rdx) (h24 : W 24 = s.gpr .r8)
    (h25 : W 25 = s.gpr .r9) (h26 : W 26 = stackArg s 15) :
    WP isa (.block privArgs) u fun u' => Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧
      Lay u' (fb s) (stackArg s 14) ∧ Frame [frR s] u.mem u'.mem ∧
      (∃ W', Rep u'.mem (fb s) (stackArg s 14) V W' ∧ (∀ i < 14, W' i = pArg s i) ∧
        (∀ i < nW, 14 ≤ i → W' i = W i)) ∧
      u'.gpr .rdi = s.gpr .rdi ∧ u'.gpr .rsi = s.gpr .rcx ∧ u'.gpr .rdx = s.gpr .rdx ∧ u'.gpr .rcx = s.gpr .rcx ∧
      u'.gpr .r8 = s.gpr .r8 ∧ u'.gpr .r9 = s.gpr .r9 := by
  rw [privArgs_eq, WP.block_append_iff]
  refine WP.mono (cpys_ok hp 10 (le_refl _) u L hrd hA R) fun u1 ⟨k1, L1, _, f1, R1⟩ => ?_
  have G' := L1.geo
  set W1 := cpW s W 10 with hW1
  have c : ∀ i, 14 ≤ i → W1 i = W i := fun i hi => by simp only [hW1, cpW]; rw [ifn (by omega)]
  have hs : u1.mem.readW (off (fb s) sScr) 64 = stackArg s 14 := L1.slot
  set S := stackArg s 14
  have Ra := R1.wf G' (k := 0) (by decide) (off S oEm)
  have Rb := Ra.wf G' (k := 1) (by decide) (s.gpr .rcx)
  have Rc := Rb.wf G' (k := 12) (by decide) (off S oRsa)
  have Rd := Rc.wf G' (k := 13) (by decide) (stackArg s 15 - BitVec.ofNat 64 1024)
  simp only [Nat.reduceMul, off_zero] at Ra Rb Rc Rd
  have hst0 : InRegions u1.wr (fb s) 8 := by simpa only [off_zero] using L1.st (d := 0) (by decide)
  have f1' : (u1.mem.writeW (fb s) (off S oEm)).readW (off (fb s) sK) 64 = s.gpr .rcx := by
    rw [Ra.rd (d := sK) 23 rfl (by decide)]; simp [upd, c, h23]
  have f2 : ((u1.mem.writeW (fb s) (off S oEm)).writeW (off (fb s) 8) (s.gpr .rcx)).readW
      (off (fb s) sScr) 64 = S := by
    rw [Rb.rd (d := sScr) 14 rfl (by decide)]; simp only [upd, Nat.reduceEqDiff, ite_false]
    exact (R1.rd (d := sScr) 14 rfl (by decide)).symm.trans hs
  have f3 : (((u1.mem.writeW (fb s) (off S oEm)).writeW (off (fb s) 8) (s.gpr .rcx)).writeW
      (off (fb s) 96) (off S oRsa)).readW (off (fb s) sScrLen) 64 = stackArg s 15 := by
    rw [Rc.rd (d := sScrLen) 26 rfl (by decide)]; simp [upd, c, h26]
  set m4 := ((((u1.mem.writeW (fb s) (off S oEm)).writeW (off (fb s) 8) (s.gpr .rcx)).writeW
      (off (fb s) 96) (off S oRsa)).writeW (off (fb s) 104) (stackArg s 15 - BitVec.ofNat 64 1024)) with hm4
  have g : ∀ k, 14 ≤ k → k < nW → m4.readW (off (fb s) (8 * k)) 64 = W k := fun k hk hk' => by
    refine (Rd.fr k hk').trans ?_; simp only [upd]; rw [ifn (by omega), ifn (by omega),
        ifn (by omega), ifn (by omega), c k hk]
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun u' => u'.mem = m4 ∧
      u'.gpr .rdi = s.gpr .rdi ∧ u'.gpr .rsi = s.gpr .rcx ∧ u'.gpr .rdx = s.gpr .rdx ∧ u'.gpr .rcx = s.gpr .rcx ∧
      u'.gpr .r8 = s.gpr .r8 ∧ u'.gpr .r9 = s.gpr .r9) ?_ rfl) fun u2 ⟨⟨hm, h1, h2, h3, h4, h5, h6⟩, k2⟩ => ?_
  · xrun [privTail, scr, VG.Impl.Mgf1.X86_64.scr, VG.Impl.RsaOaep.X86_64.lay, List.cons_append, List.nil_append,
      ea_sp, L1.rsp, L1.ld (d := sScr) (by decide), hs,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide), off_plus, hst0,
      L1.st (d := 8) (by decide), L1.st (d := 96) (by decide), L1.st (d := 104) (by decide),
      L1.ld (d := sK) (by decide), L1.ld (d := sScrLen) (by decide), L1.ld (d := sOut) (by decide),
      L1.ld (d := sN) (by decide), L1.ld (d := sE) (by decide), L1.ld (d := sEl) (by decide), f1', f2, f3,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oRsa < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show 1024 < 2 ^ 31 by decide),
      show m4.readW (off (fb s) sOut) 64 = s.gpr .rdi from (g 21 (by decide) (by decide)).trans h21,
      show m4.readW (off (fb s) sK) 64 = s.gpr .rcx from (g 23 (by decide) (by decide)).trans h23,
      show m4.readW (off (fb s) sN) 64 = s.gpr .rdx from (g 22 (by decide) (by decide)).trans h22,
      show m4.readW (off (fb s) sE) 64 = s.gpr .r8 from (g 24 (by decide) (by decide)).trans h24,
      show m4.readW (off (fb s) sEl) 64 = s.gpr .r9 from (g 25 (by decide) (by decide)).trans h25]
    rw [show BitVec.signExtend 64 (1024 : BitVec 32) = BitVec.ofNat 64 1024 by decide]
    exact ⟨rfl, (g 21 (by decide) (by decide)).trans h21, (g 23 (by decide) (by decide)).trans h23,
      (g 22 (by decide) (by decide)).trans h22, (g 23 (by decide) (by decide)).trans h23,
      (g 24 (by decide) (by decide)).trans h24, (g 25 (by decide) (by decide)).trans h25⟩
  have R2 : Rep u2.mem (fb s) S V _ := hm ▸ Rd
  have f2' : Frame [frR s] u1.mem u2.mem := by
    rw [hm, hm4]
    have h0 := frame_wF hp (m := u1.mem) (d := 0) (by decide) (off S oEm)
    rw [off_zero] at h0
    exact ((h0.trans (frame_wF hp (d := 8) (by decide) _)).trans
      (frame_wF hp (d := 96) (by decide) _)).trans (frame_wF hp (d := 104) (by decide) _)
  refine ⟨(k1.trans k2).mono (by decide), L1.of_rep' R1 R2 (by simp [upd]) (k2.gpr (by decide)) k2.2.2,
    f1.trans f2', ⟨_, R2, fun i hi => ?_, fun i hi h14 => ?_⟩, h1, h2, h3, h4, h5, h6⟩
  · simp only [upd, hW1, cpW, pArg]
    rcases (show i = 0 ∨ i = 1 ∨ (2 ≤ i ∧ i < 12) ∨ i = 12 ∨ i = 13 by omega) with h | h | h | h | h
    · subst h; simp; rfl
    · subst h; simp
    · rw [ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega), ifp h]
      match i, h with
      | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ => rfl
    · subst h; simp; rfl
    · subst h; simp
  · simp only [upd]
    rw [ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega), c i h14]

end VG.Proof.RsaPss.X86_64
