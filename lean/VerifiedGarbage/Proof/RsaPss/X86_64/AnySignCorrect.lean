module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnySignCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnySignMain
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyChecks
public import VerifiedGarbage.Proof.RsaPss.AnyHash
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect
public import VerifiedGarbage.Proof.RsaPss.SignCases
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
public import VerifiedGarbage.Proof.RsaPss.X86_64.Params
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-!
# RSASSA-PSS signing on x86-64: correctness

`sign_body`: from the entry state, the body of the frame leaves `out` and
`rax` as `RsaPss.sign` says, with the callee-saved registers restored.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (chkContract)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Impl.RsaPss.X86_64.AnyHash (emLenAny saltFitsAny)

variable {G : Spec.Mgf1.Hash}

/-- Memory changed only in the frame. -/
theorem frame_wrRA {s : State} {m : Mem} (h : Frame [frR s] s.mem m) : Frame (wrRA s) s.mem m :=
  h.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s⟩

/-- Memory changed only in the writable regions and below the frame. -/
theorem frame_keepA {s u v : State} (hp : SPreA G s) (hw : u.wr = frR s :: s.wr) (hsp : u.gpr .rsp = fb s)
    (hM : Frame (wrRA s) s.mem u.mem)
    (hk : ∀ a, (∀ r ∈ u.wr, ¬ r.Contains a 1) → ¬ (below (u.gpr .rsp) 8).Contains a 1 → v.mem a = u.mem a) :
    Frame (wrRA s) s.mem v.mem := by
  intro x hx
  refine (hk x (fun r hr hc => ?_) (fun hc => ?_)).trans (hM x hx)
  · rw [hw, hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hx _ (List.mem_cons_self ..) (frame_sub s x hc)
    · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hc
    · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hc
  · rw [hsp] at hc; exact hx _ (List.mem_cons_self ..) (ret_sub s x hc)

/-- The outcome `signAnyK.post` asks for, with the hash functions `G` and
`Gm`. -/
def signOutA (G Gm : Spec.Mgf1.Hash) (s : State) : Spec.Rsa.Outcome :=
  Spec.RsaPss.sign G Gm (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 10) G.len)
    (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat)

/-- Before the epilogue: the outcome written, the saved registers in their
slots. -/
structure SDoneA (G Gm : Spec.Mgf1.Hash) (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 14)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : Spec.Rsa.writtenOutcome t.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t.gpr .rax).setWidth 32) (signOutA G Gm s)
  /-- MXCSR's control bits. -/
  mx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem fail_doneA {s t : State} (hp : SPreA G s) {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (fb s) (stackArg s 14)) (R : Rep t.mem (fb s) (stackArg s 14) V W) (hw : t.wr = frR s :: s.wr)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r)
    (h16 : W 16 = s.gpr .rdi) (h17 : W 17 = s.gpr .rcx) (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp)
    (h43 : W 43 = s.gpr .r12) {Gm : Spec.Mgf1.Hash} (hinv : signOutA G Gm s = .invalid) (hmx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10) :
    WP isa signFail t (SDoneA G Gm s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) ∈ t.wr := by
    rw [hw, hp.hwr, ← hp.hsi]; simp
  have hO : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint (stkR s) := by rw [← hp.hsi]; exact hp.dKo.symm
  refine WP.mono_mx (by decide) (signFail_ok L R (out := s.gpr .rdi) (k := (s.gpr .rcx).toNat) h16
    (by rw [h17, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_arith) hk2 hout (by rw [← hp.hsi]; exact hp.wO)
    ((by rw [← hp.hsi]; exact hp.dOs : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint
      ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩).sub_right (Region.sub_prefix (by have := hp.hsl; unfold oRsa; omega_arith)))
    (hO.sub_right (frame_sub s))) fun t' ⟨L', k', R', hax, hz, _⟩ hm => ?_
  refine ⟨L', k'.2.2.trans hw, fun r hr => (k'.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide)).trans
    (hcs r hr), ?_, ?_, ?_, ?_, by rw [hm]; exact hmx⟩
  · rw [R'.rd (d := sRbx) 41 rfl (by decide), h41]
  · rw [R'.rd (d := sRbp) 42 rfl (by decide), h42]
  · rw [R'.rd (d := sR12) 43 rfl (by decide), h43]
  · rw [hinv]; exact ⟨by rw [hax]; rfl, hz⟩

/-- Stack arguments, kept where the function does not write. -/
theorem argsKept_ofA {s : State} (hp : SPreA G s) {m : Mem} (hM : Frame (wrRA s) s.mem m) : ArgsKeptA s m := by
  intro j hj
  refine hM.readW (r := ⟨stackArgAddr s 0, 144⟩) ?_ (in_apartA hp.dKa hp.dOa hp.dsa.symm) (by decide)
  rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_arith]
  have := hp.sp2
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- An input's bytes, unchanged. -/
theorem bytesF_eqA {s : State} {m : Mem} (hM : Frame (wrRA s) s.mem m) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ wrRA s, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    (List.range n).map (bytesF m p) = Spec.Rsa.bytesAt s.mem p n :=
  bytesAt_frame hM hd hn

/-- After the checks: the encoding, the private-key operation, and its
outcome. -/
theorem main_doneA {hs : List Hash} {kh g : Nat} (hkh : kh < hs.length) (hg : g < hs.length)
    (hl : hs.length ≤ 2 ^ 31) (ht : TierOk hs)
    {H : Hash} (hkH : hs[kh] = H) (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)
    (lk : Pbkdf2.Md.X86_64.MgfLink H hH)
    (hG : Pbkdf2.Md.X86_64.HashOK hs[g]) (KG : Pbkdf2.Md.X86_64.Callees hs[g]) (lkG : Pbkdf2.Md.X86_64.MgfLink hs[g] hG)
    {privN : String} {privC : Prog isa}
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hspC : SpSafe privC) (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes)
    {s u : State} (hp : SPreA lk.G s) {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay u (fb s) (stackArg s 14)) (R : Rep u.mem (fb s) (stackArg s 14) V W) (hw : u.wr = frR s :: s.wr)
    (hrd : u.rd = s.rd) (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], u.gpr r = s.gpr r) (hM : Frame (wrRA s) s.mem u.mem)
    {lo : Nat} {c : Byte}
    (h16 : W 16 = s.gpr .rdi) (h17 : W 17 = s.gpr .rcx) (h18 : W 18 = s.gpr .rdx) (h19 : W 19 = s.gpr .r8)
    (h20 : W 20 = s.gpr .r9) (h22 : W 22 = stackArg s 15) (h25 : W 25 = BitVec.setWidth 64 c)
    (h26 : W 26 = BitVec.ofNat 64 lo) (h37 : W 37 = stackArg s 10) (h39 : W 39 = stackArg s 12)
    (h40 : W 40 = stackArg s 13) (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp) (h43 : W 43 = s.gpr .r12)
    (h15 : W 15 = BitVec.ofNat 64 H.D) (h47 : W 47 = BitVec.ofNat 64 kh) (h48 : W 48 = BitVec.ofNat 64 g)
    (hlo : lo ≤ 1) (hfit : H.D + (stackArg s 13).toNat + 2 ≤ (s.gpr .rcx).toNat - lo)
    (hax : u.gpr .rax = BitVec.ofNat 64 ((s.gpr .rcx).toNat - lo - (H.D + 2)))
    (hspec : signOutA lk.G lkG.G s = Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      ((List.range (s.gpr .rcx).toNat).map (RsaPss.emT lo ((s.gpr .rcx).toNat - lo - H.D - 1) (stackArg s 13).toNat
        (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat)
        (lk.G.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (stackArg s 10) H.D ++
          Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat))
        (Spec.Mgf1.mgf1 lkG.G (lk.G.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (stackArg s 10) H.D ++
          Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat)) ((s.gpr .rcx).toNat - lo - H.D - 1)) c))
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))
    (hmx : u.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10) :
    WP isa (AnyHash.signMain hs privN privC) u (SDoneA lk.G lkG.G s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD : H.D = lk.G.len := lk.len.symm
  have hsl : (stackArg s 13).toNat < 2 ^ 64 := (stackArg s 13).isLt
  have dg : ∀ r ∈ wrRA s, (⟨stackArg s 10, H.D⟩ : Region).Disjoint r := by
    rw [hD]; exact in_apartA hp.dKdg hp.dOdg hp.ddgs
  have sa : ∀ r ∈ wrRA s, (⟨stackArg s 12, (stackArg s 13).toNat⟩ : Region).Disjoint r :=
    in_apartA hp.dKsa hp.dOsa hp.dsas
  have hdg : (stackArg s 10).toNat + H.D ≤ 2 ^ 64 := by rw [hD]; exact hp.wDg
  have hsa := hp.wSa
  rw [AnyHash.signMain]
  simp only [seqs]
  -- The encoding.
  refine WP.seq (WP.mono_mx (safe_mx (signEncAny_safe ht)) (WP.keepIn (signEncAny_safe ht) (signEncAny_xd ht)
    (signEncAny_ok hkh hg hl hkH hH K lk hG KG lkG L R (k := (s.gpr .rcx).toNat) (lo := lo) (sl := (stackArg s 13).toNat)
      (c := c) (by rw [h17, BitVec.ofNat_toNat, BitVec.setWidth_eq]) h26 h25 h37 h39
      (by rw [h40, BitVec.ofNat_toNat, BitVec.setWidth_eq]) h15 h47 h48 hk1 hk2 hlo hfit hax
      (fun i hi => ⟨⟨stackArg s 10, lk.G.len⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
      (fun i hi => by
        have := hp.outside lk.G hp.dOdg hp.ddgs hp.dKdg (a := stackArg s 10 + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by omega_arith) (by omega_arith))
        rwa [← hw] at this)
      (fun i hi => ⟨⟨stackArg s 12, (stackArg s 13).toNat⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
      (fun i hi => by
        have := hp.outside lk.G hp.dOsa hp.dsas hp.dKsa (a := stackArg s 12 + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by omega_arith) (by omega_arith))
        rwa [← hw] at this)))
    fun u1 ⟨⟨L1, rd1, wr1, cs1, V1, W1, R1, hW1, hV1⟩, f1⟩ hm1 => ?_)
  have hM1 := frame_keepA hp hw L.rsp hM f1
  have hw1 : u1.wr = frR s :: s.wr := wr1.trans hw
  have g : ∀ j, j < nW → j < 23 → W1 j = W j := fun j hj h => hW1 j hj (.inl h)
  -- The private-key operation's arguments.
  refine WP.seq (WP.mono_mx (by decide) (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (privArgs_okA hp L1 (rd1.trans hrd) (argsKept_ofA hp hM1) R1 ((g 16 (by decide) (by decide)).trans h16)
      ((g 17 (by decide) (by decide)).trans h17) ((g 18 (by decide) (by decide)).trans h18)
      ((g 19 (by decide) (by decide)).trans h19) ((g 20 (by decide) (by decide)).trans h20)
      ((g 22 (by decide) (by decide)).trans h22)))
    fun u2 ⟨⟨k2, L2, ⟨W2, R2, hW2a, hW2b⟩, h2di, h2si, h2dx, h2cx, h2r8, h2r9⟩, f2⟩ hm2 => ?_)
  have hw2 : u2.wr = frR s :: s.wr := k2.2.2.trans hw1
  have hM2 := frame_keepA hp hw1 L1.rsp hM1 f2
  -- The call.
  refine WP.mono (priv_callA hv hspC hdC hp L2.rsp ((k2.2.1.trans rd1).trans hrd) hw2 hM2
    (fun i hi => (R2.fr i (by unfold nW frameBytes; omega_arith)).trans (hW2a i hi)) h2di h2si h2dx h2cx h2r8 h2r9)
    fun u3 ⟨rd3, wr3, cs3, mx3, _, hk3, hout3⟩ => ?_
  have R3 : Rep u3.mem (fb s) (stackArg s 14) V1 W2 := R2.of_keep L2.geo fun x hx => hk3 x hx
  have L3 : Lay u3 (fb s) (stackArg s 14) :=
    L2.of_rep' R2 R3 rfl (cs3 .rsp (by decide)) wr3
  have w : ∀ j, 32 < j → j < nW → W2 j = W j := fun j h hj =>
    (hW2b j hj (by omega_arith)).trans (hW1 j hj (.inr h))
  refine ⟨L3, wr3.trans hw2, fun r hr => ?_, ?_, ?_, ?_, ?_, by rw [mx3, hm2, hm1]; exact hmx⟩
  · have hr3 : r = .r13 ∨ r = .r14 ∨ r = .r15 := by simpa using hr
    have h1 : r ∈ calleeSaved := by rcases hr3 with rfl | rfl | rfl <;> decide
    have h2 : r ∉ [Reg.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] := by rcases hr3 with rfl | rfl | rfl <;> decide
    have h3 : r ∈ [Reg.r13, .r14, .r15, .rsp] := by rcases hr3 with rfl | rfl | rfl <;> decide
    rw [cs3 r h1, k2.gpr h2, cs1 r h3, hcs r hr]
  · rw [R3.rd (d := sRbx) 41 rfl (by decide), w 41 (by decide) (by decide), h41]
  · rw [R3.rd (d := sRbp) 42 rfl (by decide), w 42 (by decide) (by decide), h42]
  · rw [R3.rd (d := sR12) 43 rfl (by decide), w 43 (by decide) (by decide), h43]
  · have hem : Spec.Rsa.bytesAt u2.mem (off (stackArg s 14) oEm) (s.gpr .rcx).toNat =
        (List.range (s.gpr .rcx).toNat).map (fun i => V1 (oEm + i)) := by
      rw [bytesAt_off]
      exact List.map_congr_left fun i hi => R2.scr _ (by have := List.mem_range.mp hi; unfold oEm oRsa; omega_arith)
    rw [hem, List.map_congr_left (fun i hi => hV1 i (List.mem_range.mp hi)),
      bytesF_eqA hM dg (by omega_arith), bytesF_eqA hM sa (by omega_arith)] at hout3
    rw [hspec]
    exact hout3

/-- The modulus' first byte. -/
theorem n0_okA {s t : State} (hp : SPreA G s) (L : Lay t (fb s) (stackArg s 14)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 14) V W) (h18 : W 18 = s.gpr .rdx) (hrd : t.rd = s.rd)
    (hf : Frame (wrRA s) s.mem t.mem) :
    WP isa (.block n0) t fun t' => Keep [.rsi, .rax] t t' ∧ t'.mem = t.mem ∧
      t'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdx)).toNat ∧
      t'.zf = some (decide ((s.mem (s.gpr .rdx)).toNat = 0)) := by
  have hk1 := hp.k1
  have hn : t.mem (s.gpr .rdx) = s.mem (s.gpr .rdx) := by
    have := hf.bytes (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) (in_apartA hp.dKn hp.dOn hp.dns) (by dsimp only; have := hp.wN; omega_arith)
      (i := 0) (by dsimp only; omega_arith)
    simpa using this
  have hin : InRegions (t.rd ++ t.wr) (s.gpr .rdx) 1 :=
    ⟨⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith⟩
  refine WP.mono (WP.keep [.rsi, .rax] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdx)).toNat ∧
      t'.zf = some (decide ((s.mem (s.gpr .rdx)).toNat = 0))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨k, h⟩
  xrun [n0, ea_sp, ea_at0, L.rsp, L.ld (d := sN) (by decide), R.rd (d := sN) 18 rfl (by decide), h18, hin, hn]
  rw [zext8, BitVec.and_self, ofNat_beq_zero (by have := (s.mem (s.gpr .rdx)).isLt; omega_arith)]
  exact ⟨rfl, rfl⟩

theorem restore_okA {s t : State} (hp : SPreA G s) {Gm : Spec.Mgf1.Hash}
    (hGm : Spec.HashId.mgf1 (msel s) = some Gm) (D : SDoneA G Gm s t) :
    WP isa (.block restoreRegs) t fun t' => t'.gpr .rsp = fb s ∧ t'.wr = (allocState frameBytes s).wr ∧
      (∀ r ∈ calleeSaved, (freedF t').gpr r = s.gpr r) ∧ signAnyK.post s (freedF t') ∧
      (freedF t').mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hF := fb_toNatA hp
  refine WP.mono_mx (by decide) (WP.keep [.rbx, .rbp, .r12] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rbx = s.gpr .rbx ∧
      t'.gpr .rbp = s.gpr .rbp ∧ t'.gpr .r12 = s.gpr .r12) ?_ rfl) fun t' ⟨⟨hm, h1, h2, h3⟩, k⟩ hmx => ?_
  · xrun [restoreRegs, ea_sp, D.L.rsp, D.L.ld (d := sRbx) (by decide), D.L.ld (d := sRbp) (by decide),
      D.L.ld (d := sR12) (by decide), D.rbx, D.rbp, D.r12]
  have hsp : t'.gpr .rsp = fb s := (k.gpr (by decide)).trans D.L.rsp
  refine ⟨hsp, k.2.2.trans D.wr, fun r hr => ?_, ?_, by show t'.mxcsr.extractLsb' 6 10 = _; rw [hmx]; exact D.mx⟩
  · simp only [freedF, State.setReg]
    by_cases hr' : r = .rsp
    · subst hr'; simp only [ite_true, hsp, fb]; exact BitVec.sub_add_cancel _ _
    · simp only [hr', ite_false]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact absurd rfl hr'
      · exact h3
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
  · intro H' G' h1 h2
    obtain rfl : H' = G := Option.some.inj (h1.symm.trans hp.hG)
    obtain rfl : G' = Gm := Option.some.inj (h2.symm.trans hGm)
    show Spec.Rsa.writtenOutcome t'.mem _ _ ((t'.gpr .rax).setWidth 32) _
    rw [hm, k.gpr (show Reg.rax ∉ [Reg.rbx, .rbp, .r12] by decide), hp.hdl]
    exact D.out

theorem sign_okA {hs : List Hash} {kh g : Nat} (hkh : kh < hs.length) (hg : g < hs.length)
    (hl : hs.length ≤ 2 ^ 31) (ht : TierOk hs)
    {H : Hash} (hkH : hs[kh] = H) (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)
    (lk : Pbkdf2.Md.X86_64.MgfLink H hH)
    (hG : Pbkdf2.Md.X86_64.HashOK hs[g]) (KG : Pbkdf2.Md.X86_64.Callees hs[g]) (lkG : Pbkdf2.Md.X86_64.MgfLink hs[g] hG)
    {privN : String} {privC : Prog isa}
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hspC : SpSafe privC) (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes) {s : State}
    (h : signAnyK.pre s) (hsk : hsel s = kh) (hsg : msel s = g) (hHs : Spec.HashId.mgf1 kh = some lk.G)
    (hGs : Spec.HashId.mgf1 g = some lkG.G) :
    WP isa (AnyHash.sign hs privN privC) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ signAnyK.post s s' ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hp := SPreA.of lk.G h (by rw [hsk]; exact hHs)
  have e11 : stackArg s 11 = BitVec.ofNat 64 H.D := by
    rw [← lk.len, ← hp.hdl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have e16 : stackArg s 16 = BitVec.ofNat 64 kh := by rw [← hsk, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have e17 : stackArg s 17 = BitVec.ofNat 64 g := by rw [← hsg, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hF := fb_toNatA hp
  have hk1 := hp.k1; have hk2 := hp.k2
  refine wp_frame (by have := hp.sp1; unfold signStack Rsa.X86_64.stackBytes frameBytes at *; omega_arith) ?_
  rw [AnyHash.signBody]
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_mx (by decide) (signPro_okA hp) fun t1 ⟨k1, L1, R1, f1⟩ hx1 => ?_
  refine WP.mono_mx (by decide) (n0_okA hp L1 R1 (by simp [proWA, upd]) k1.2.1 (frame_wrRA f1)) fun t2 ⟨k2, hm2, hax2, hz2⟩ hx2 => ?_
  have L2 : Lay t2 (fb s) (stackArg s 14) := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  have R2 : Rep t2.mem (fb s) (stackArg s 14) _ (proWA s) := hm2 ▸ R1
  have hM2 : Frame (wrRA s) s.mem t2.mem := hm2 ▸ frame_wrRA f1
  have hw2 : t2.wr = frR s :: s.wr := k2.2.2.trans k1.2.2
  have hrd2 : t2.rd = s.rd := k2.2.1.trans k1.2.1
  have hcs2 : ∀ r ∈ [Reg.r13, .r14, .r15], t2.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.rsi, .rax] := by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k2.gpr this, k1.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)]
    simp only [allocState_gpr']; rw [ifn (by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)]
  refine WP.seq (WP.mono (Q := SDoneA lk.G lkG.G s) ?_ fun t3 D => restore_okA hp (by rw [hsg]; exact hGs) D)
  -- The modulus as `n₀ ‖ rest`.
  set n₀ := s.mem (s.gpr .rdx) with hn₀
  set rest := Spec.Rsa.bytesAt s.mem (s.gpr .rdx + 1) ((s.gpr .rcx).toNat - 1) with hrest
  have hnB : Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = n₀ :: rest := bytesAt_cons _ _ (by omega_arith)
  have hrl : (n₀ :: rest).length = (s.gpr .rcx).toNat := by
    rw [← hnB]; simp [Spec.Rsa.bytesAt]
  have hout : signOutA lk.G lkG.G s = Spec.RsaPss.sign lk.G lkG.G (n₀ :: rest)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 10) lk.G.len)
      (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat) := by rw [signOutA, hnB]
  have hfail : ∀ {t : State} {V : Nat → Byte} {W : Nat → BitVec 64}, Lay t (fb s) (stackArg s 14) →
      Rep t.mem (fb s) (stackArg s 14) V W → t.wr = frR s :: s.wr →
      (∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r) → W 16 = s.gpr .rdi → W 17 = s.gpr .rcx →
      W 41 = s.gpr .rbx → W 42 = s.gpr .rbp → W 43 = s.gpr .r12 → signOutA lk.G lkG.G s = .invalid →
      t.mxcsr = s.mxcsr →
      WP isa signFail t (SDoneA lk.G lkG.G s) := fun L R hw hcs a b c d e f hx => fail_doneA hp L R hw hcs a b c d e f (by rw [hx])
  have hz : ∀ b : Bool, t2.zf = some b → (b = true ↔ n₀.toNat = 0) := fun b hb => by
    rw [hz2] at hb; cases hb; simp
  refine WP.ite (M := isa) _ (show isa.eval .e t2 = _ from hz2) (fun hb => ?_) (fun hb => ?_)
  · -- `n₀ = 0`: refused.
    rw [decide_eq_true_eq] at hb
    have h0 : n₀ = 0 := BitVec.eq_of_toNat_eq hb
    refine hfail L2 R2 hw2 hcs2 (by simp [proWA, upd]) (by simp [proWA, upd]) (by simp [proWA, upd])
      (by simp [proWA, upd]) (by simp [proWA, upd]) ?_ (by rw [hx2, hx1]; rfl)
    rw [hout, h0]; exact Any.sign_zero ..
  rw [decide_eq_false_iff_not] at hb
  have h0 : n₀ ≠ 0 := fun h => hb (by rw [h]; rfl)
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have hGl : lk.G.len = H.D := lk.len
  have hEL := emLen_eq (rest := rest) h0
  rw [hrl] at hEL
  have hlo : loV n₀.toNat ≤ 1 := by unfold loV; split <;> omega_arith
  -- `smear(n₀ >> 1)`.
  refine WP.seq (WP.mono_mx (by decide) (smear_ok t2 (x := n₀.toNat) n₀.isLt hb hax2) fun t3 ⟨k3, hm3, hdx3, hz3⟩ hx3 => ?_)
  have L3 : Lay t3 (fb s) (stackArg s 14) := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have R3 : Rep t3.mem (fb s) (stackArg s 14) _ (proWA s) := hm3 ▸ R2
  -- `emLen`, the mask and `lo`.
  have h15 : proWA s 15 = BitVec.ofNat 64 H.D := by simp only [proWA, upd]; exact e11
  have h47 : proWA s 47 = BitVec.ofNat 64 kh := by simp only [proWA, upd]; exact e16
  have h48 : proWA s 48 = BitVec.ofNat 64 g := by simp only [proWA, upd]; exact e17
  refine WP.seq (WP.mono_mx (safe_mx (by safe_by [emLenAny])) (WP.keepIn (by safe_by [emLenAny]) (by exact Nat.zero_le 8)
    (emLenAny_ok (D := H.D) (by omega_arith) L3 R3 (x := n₀.toNat) (k := (s.gpr .rcx).toNat)
      (by simp [proWA, upd]) h15 (by omega_arith) (by omega_arith) hdx3 hz3)) fun t4 ⟨⟨L4, k4, R4, hax4, hc4⟩, f4⟩ hx4 => ?_)
  have hw4 : t4.wr = frR s :: s.wr := k4.2.2.trans (k3.2.2.trans hw2)
  have hM4 : Frame (wrRA s) s.mem t4.mem :=
    frame_keepA hp (k3.2.2.trans hw2) L3.rsp (hm3 ▸ hM2) f4
  have hcs4 : ∀ r ∈ [Reg.r13, .r14, .r15], t4.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.rdx, .r8, .rax, .r9] := by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k4.gpr this, k3.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), hcs2 r hr]
  refine WP.ite (M := isa) _ (show isa.eval .b t4 = _ from hc4) (fun hb4 => ?_) (fun hb4 => ?_)
  · -- `emLen < hLen + 2`: refused.
    rw [decide_eq_true_eq] at hb4
    refine hfail L4 R4 hw4 hcs4 (by simp [proWA, upd]) (by simp [proWA, upd]) (by simp [proWA, upd])
      (by simp [proWA, upd]) (by simp [proWA, upd]) ?_ (by rw [hx4, hx3, hx2, hx1]; rfl)
    rw [hout]
    exact Any.sign_long _ _ _ _ _ _ _ _ _ _ (by rw [emLen_eq h0, hrl, hGl]; omega_arith)
  rw [decide_eq_false_iff_not] at hb4
  -- The salt fits.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_mx (by decide) (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = stackArg s 13 ∧ t.mem = t4.mem) (by
    xrun [ea_sp, L4.rsp, L4.ld (d := sSaltLen) (by decide), R4.rd (d := sSaltLen) 40 rfl (by decide)]
    simp [upd, proWA]) rfl) fun t5 ⟨⟨hdx5, hm5⟩, k5⟩ hx5 => ?_
  have L5 : Lay t5 (fb s) (stackArg s 14) := L4.congr (k5.gpr (by decide)) k5.2.2 (by rw [hm5])
  refine WP.mono_mx (safe_mx (by safe_by [saltFitsAny])) (saltFitsAny_ok (D := H.D) L5 (hm5 ▸ R4)
    ((upd_ne _ (by decide)).trans ((upd_ne _ (by decide)).trans h15))
    (a := (s.gpr .rcx).toNat - loV n₀.toNat)
    (b := stackArg s 13) (by omega_arith) (by omega_arith) (by rw [k5.gpr (by decide)]; exact hax4) hdx5)
    fun t6 ⟨k6, hm6, hax6, hc6⟩ hx6 => ?_
  have L6 : Lay t6 (fb s) (stackArg s 14) := L4.congr ((k6.gpr (by decide)).trans (k5.gpr (by decide)))
    (k6.2.2.trans k5.2.2) (by rw [hm6, hm5])
  have hm65 : t6.mem = t4.mem := by rw [hm6, hm5]
  have R6 := hm65 ▸ R4
  have hw6 : t6.wr = frR s :: s.wr := k6.2.2.trans (k5.2.2.trans hw4)
  have hcs6 : ∀ r ∈ [Reg.r13, .r14, .r15], t6.gpr r = s.gpr r := fun r hr => by
    rw [k6.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp),
      k5.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), hcs4 r hr]
  refine WP.ite (M := isa) _ (show isa.eval .b t6 = _ from hc6) (fun hb6 => ?_) (fun hb6 => ?_)
  · -- The salt does not fit: refused.
    rw [decide_eq_true_eq] at hb6
    refine hfail L6 R6 hw6 hcs6 (by simp [proWA, upd]) (by simp [proWA, upd]) (by simp [proWA, upd])
      (by simp [proWA, upd]) (by simp [proWA, upd]) ?_ (by rw [hx6, hx5, hx4, hx3, hx2, hx1]; rfl)
    rw [hout]
    exact Any.sign_long _ _ _ _ _ _ _ _ _ _ (by rw [emLen_eq h0, hrl, hGl, bytesAt_length]; omega_arith)
  rw [decide_eq_false_iff_not] at hb6
  -- The encoding and the private-key operation.
  have hfit : H.D + (stackArg s 13).toNat + 2 ≤ (s.gpr .rcx).toNat - loV n₀.toNat := by omega_arith
  have hrd6 : t6.rd = s.rd := k6.2.1.trans (k5.2.1.trans (k4.2.1.trans (k3.2.1.trans hrd2)))
  have hlo' : (n₀ :: rest).length - Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (n₀ :: rest)) - 1) =
      loV n₀.toNat := by rw [emLen_eq h0, hrl]; omega_arith
  refine main_doneA hkh hg hl ht hkH hH K lk hG KG lkG hv hspC hdC hp L6 R6 hw6 hrd6 hcs6 (hm65 ▸ hM4) (lo := loV n₀.toNat)
    (c := (0xFF : Byte) >>> (8 * Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (n₀ :: rest)) - 1) -
      (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (n₀ :: rest)) - 1)))
    (by simp [proWA, upd]) (by simp [proWA, upd]) (by simp [proWA, upd]) (by simp [proWA, upd]) (by simp [proWA, upd])
    (by simp [proWA, upd]) (by simp only [upd, Nat.reduceEqDiff, ite_true, ite_false]; exact maskV_eq rest h0)
    (by simp [upd]) (by simp [proWA, upd]) (by simp [proWA, upd]) (by simp [proWA, upd]) (by simp [proWA, upd])
    (by simp [proWA, upd]) (by simp [proWA, upd])
    ((upd_ne _ (by decide)).trans ((upd_ne _ (by decide)).trans h15))
    ((upd_ne _ (by decide)).trans ((upd_ne _ (by decide)).trans h47))
    ((upd_ne _ (by decide)).trans ((upd_ne _ (by decide)).trans h48))
    hlo hfit hax6 ?_ (by rw [hx6, hx5, hx4, hx3, hx2, hx1]; rfl)
  rw [hout, Any.sign_eq lk.G lkG.G (validG hH lk.hash lk.len) (validG hG lkG.hash lkG.len) h0 (by rw [bytesAt_length]) rfl rfl hlo'
    (by rw [emLen_eq h0, hrl, hGl]) (by rw [emLen_eq h0, hrl, hGl, bytesAt_length]; omega_arith), hnB, hrl, hGl,
    bytesAt_length]

end VG.Proof.RsaPss.X86_64.Any
