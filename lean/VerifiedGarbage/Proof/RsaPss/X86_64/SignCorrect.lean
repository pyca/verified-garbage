import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
import VerifiedGarbage.Proof.RsaPss.SignCases

/-!
# RSASSA-PSS signing on x86-64: correctness

`sign_body`: from the entry state, the body of the frame leaves `out` and
`rax` as `RsaPss.sign` says, with the callee-saved registers restored.
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (chkContract)

variable {G : Spec.Mgf1.Hash}

theorem bytesAt_cons (m : Mem) (p : Addr) {k : Nat} (hk : 1 ≤ k) :
    Spec.Rsa.bytesAt m p k = m p :: Spec.Rsa.bytesAt m (p + 1) (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_sub_cancel]
  refine congrArg₂ _ (by simp) (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, BitVec.add_assoc]
  rw [show (1 : Addr) + BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 1) by
    rw [BitVec.add_comm, ← BitVec.ofNat_add_ofNat]; rfl]

/-- `Rep` across a change that keeps the frame and our working space. -/
theorem Rep.of_keep {m m' : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W)
    (G' : Geo F S) (hk : ∀ x, ((⟨F, frameBytes⟩ : Region).Contains x 1 ∨ (⟨S, oRsa⟩ : Region).Contains x 1) →
      m' x = m x) : Rep m' F S V W where
  scr o ho := by rw [hk _ (.inr (Offset.contains_base _ (by omega) (by unfold oRsa at *; omega))), R.scr o ho]
  fr k hk' := by
    rw [← R.fr k hk']
    refine Mem.readW_congr fun i hi => hk _ (.inl ?_)
    have := G'.Fw
    rw [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega)

/-- Memory changed only in the frame. -/
theorem frame_wrR {s : State} {m : Mem} (h : Frame [frR s] s.mem m) : Frame (wrR s) s.mem m :=
  h.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s⟩

/-- Memory changed only in the writable regions and below the frame. -/
theorem frame_keep {s u v : State} (hp : SPre G s) (hw : u.wr = frR s :: s.wr) (hsp : u.gpr .rsp = fb s)
    (hM : Frame (wrR s) s.mem u.mem)
    (hk : ∀ a, (∀ r ∈ u.wr, ¬ r.Contains a 1) → ¬ (below (u.gpr .rsp) 8).Contains a 1 → v.mem a = u.mem a) :
    Frame (wrR s) s.mem v.mem := by
  intro x hx
  refine (hk x (fun r hr hc => ?_) (fun hc => ?_)).trans (hM x hx)
  · rw [hw, hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hx _ (List.mem_cons_self ..) (frame_sub s x hc)
    · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hc
    · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hc
  · rw [hsp] at hc; exact hx _ (List.mem_cons_self ..) (ret_sub s x hc)

variable (G) in
/-- The outcome `signK.post` asks for. -/
def signOut (s : State) : Spec.Rsa.Outcome :=
  Spec.RsaPss.sign G G (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 10) G.len)
    (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat)

variable (G) in
/-- Before the epilogue: the outcome written, the saved registers in their
slots. -/
structure SDone (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 13)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : Spec.Rsa.writtenOutcome t.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t.gpr .rax).setWidth 32) (signOut G s)

theorem fail_done {s t : State} (hp : SPre G s) {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (fb s) (stackArg s 13)) (R : Rep t.mem (fb s) (stackArg s 13) V W) (hw : t.wr = frR s :: s.wr)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r)
    (h16 : W 16 = s.gpr .rdi) (h17 : W 17 = s.gpr .rcx) (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp)
    (h43 : W 43 = s.gpr .r12) (hinv : signOut G s = .invalid) :
    WP isa signFail t (SDone G s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) ∈ t.wr := by
    rw [hw, hp.hwr, ← hp.hsi]; simp
  have hO : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint (stkR s) := by rw [← hp.hsi]; exact hp.dKo.symm
  refine WP.mono (signFail_ok L R (out := s.gpr .rdi) (k := (s.gpr .rcx).toNat) h16
    (by rw [h17, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega) hk2 hout (by rw [← hp.hsi]; exact hp.wO)
    ((by rw [← hp.hsi]; exact hp.dOs : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint
      ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩).sub_right (Region.sub_prefix (by have := hp.hsl; unfold oRsa; omega)))
    (hO.sub_right (frame_sub s))) fun t' ⟨L', k', R', hax, hz, _⟩ => ?_
  refine ⟨L', k'.2.2.trans hw, fun r hr => (k'.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide)).trans
    (hcs r hr), ?_, ?_, ?_, ?_⟩
  · rw [R'.rd (d := sRbx) 41 rfl (by decide), h41]
  · rw [R'.rd (d := sRbp) 42 rfl (by decide), h42]
  · rw [R'.rd (d := sR12) 43 rfl (by decide), h43]
  · rw [hinv]; exact ⟨by rw [hax]; rfl, hz⟩

/-- Stack arguments, kept where the function does not write. -/
theorem argsKept_of {s : State} (hp : SPre G s) {m : Mem} (hM : Frame (wrR s) s.mem m) : ArgsKept s m := by
  intro j hj
  refine hM.readW (r := ⟨stackArgAddr s 0, 120⟩) ?_ (in_apart hp.dKa hp.dOa hp.dsa.symm) (by decide)
  rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
  have := hp.sp2
  exact Offset.contains_base _ (by omega) (by omega)

/-- An input's bytes, unchanged. -/
theorem bytesF_eq {s : State} {m : Mem} (hM : Frame (wrR s) s.mem m) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ wrR s, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    (List.range n).map (bytesF m p) = Spec.Rsa.bytesAt s.mem p n :=
  bytesAt_frame hM hd hn

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

include hH K in
/-- After the checks: the encoding, the private-key operation, and its
outcome. -/
theorem main_done (lk : Pbkdf2.Md.X86_64.MgfLink H hH) {privN : String} {privC : Prog isa}
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hspC : SpSafe privC) (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes - 8)
    {s u : State} (hp : SPre lk.G s) {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay u (fb s) (stackArg s 13)) (R : Rep u.mem (fb s) (stackArg s 13) V W) (hw : u.wr = frR s :: s.wr)
    (hrd : u.rd = s.rd) (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], u.gpr r = s.gpr r) (hM : Frame (wrR s) s.mem u.mem)
    {lo : Nat} {c : Byte}
    (h16 : W 16 = s.gpr .rdi) (h17 : W 17 = s.gpr .rcx) (h18 : W 18 = s.gpr .rdx) (h19 : W 19 = s.gpr .r8)
    (h20 : W 20 = s.gpr .r9) (h22 : W 22 = stackArg s 14) (h25 : W 25 = BitVec.setWidth 64 c)
    (h26 : W 26 = BitVec.ofNat 64 lo) (h37 : W 37 = stackArg s 10) (h39 : W 39 = stackArg s 11)
    (h40 : W 40 = stackArg s 12) (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp) (h43 : W 43 = s.gpr .r12)
    (hlo : lo ≤ 1) (hfit : H.D + (stackArg s 12).toNat + 2 ≤ (s.gpr .rcx).toNat - lo)
    (hax : u.gpr .rax = BitVec.ofNat 64 ((s.gpr .rcx).toNat - lo - (H.D + 2)))
    (hspec : signOut lk.G s = Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      ((List.range (s.gpr .rcx).toNat).map (RsaPss.emT lo ((s.gpr .rcx).toNat - lo - H.D - 1) (stackArg s 12).toNat
        (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat)
        (lk.G.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (stackArg s 10) H.D ++
          Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat))
        (Spec.Mgf1.mgf1 lk.G (lk.G.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (stackArg s 10) H.D ++
          Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat)) ((s.gpr .rcx).toNat - lo - H.D - 1)) c))
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)) :
    WP isa (signMain H privN privC) u (SDone lk.G s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD : H.D = lk.G.len := lk.len.symm
  have hsl : (stackArg s 12).toNat < 2 ^ 64 := (stackArg s 12).isLt
  have dg : ∀ r ∈ wrR s, (⟨stackArg s 10, H.D⟩ : Region).Disjoint r := by
    rw [hD]; exact in_apart hp.dKdg hp.dOdg hp.ddgs
  have sa : ∀ r ∈ wrR s, (⟨stackArg s 11, (stackArg s 12).toNat⟩ : Region).Disjoint r :=
    in_apart hp.dKsa hp.dOsa hp.dsas
  have hdg : (stackArg s 10).toNat + H.D ≤ 2 ^ 64 := by rw [hD]; exact hp.wDg
  have hsa := hp.wSa
  rw [signMain]
  simp only [seqs]
  -- The encoding.
  refine WP.seq (WP.mono (WP.keepIn (signEnc_safe hH K) (by rw [signEnc_xd K])
    (signEnc_ok hH K lk L R (k := (s.gpr .rcx).toNat) (lo := lo) (sl := (stackArg s 12).toNat) (c := c)
      (by rw [h17, BitVec.ofNat_toNat, BitVec.setWidth_eq]) h26 h25 h37 h39
      (by rw [h40, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hk1 hk2 hlo hfit hax
      (fun i hi => ⟨⟨stackArg s 10, lk.G.len⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by omega) (by omega)⟩)
      (fun i hi => by
        have := hp.outside lk.G hp.dOdg hp.ddgs hp.dKdg (a := stackArg s 10 + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by omega) (by omega))
        rwa [← hw] at this)
      (fun i hi => ⟨⟨stackArg s 11, (stackArg s 12).toNat⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by omega) (by omega)⟩)
      (fun i hi => by
        have := hp.outside lk.G hp.dOsa hp.dsas hp.dKsa (a := stackArg s 11 + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by omega) (by omega))
        rwa [← hw] at this)))
    fun u1 ⟨⟨L1, rd1, wr1, cs1, V1, W1, R1, hW1, hV1⟩, f1⟩ => ?_)
  have hM1 := frame_keep hp hw L.rsp hM f1
  have hw1 : u1.wr = frR s :: s.wr := wr1.trans hw
  have g : ∀ j, j < nW → j < 23 → W1 j = W j := fun j hj h => hW1 j hj (.inl h)
  -- The private-key operation's arguments.
  refine WP.seq (WP.mono (WP.keepIn (by decide) (by simp [Code.x86_64Depth])
    (privArgs_ok hp L1 (rd1.trans hrd) (argsKept_of hp hM1) R1 ((g 16 (by decide) (by decide)).trans h16)
      ((g 17 (by decide) (by decide)).trans h17) ((g 18 (by decide) (by decide)).trans h18)
      ((g 19 (by decide) (by decide)).trans h19) ((g 20 (by decide) (by decide)).trans h20)
      ((g 22 (by decide) (by decide)).trans h22)))
    fun u2 ⟨⟨k2, L2, ⟨W2, R2, hW2a, hW2b⟩, h2di, h2si, h2dx, h2cx, h2r8, h2r9⟩, f2⟩ => ?_)
  have hw2 : u2.wr = frR s :: s.wr := k2.2.2.trans hw1
  have hM2 := frame_keep hp hw1 L1.rsp hM1 f2
  -- The call.
  refine WP.mono (priv_call hv hspC hdC hp L2.rsp ((k2.2.1.trans rd1).trans hrd) hw2 hM2
    (fun i hi => (R2.fr i (by unfold nW frameBytes; omega)).trans (hW2a i hi)) h2di h2si h2dx h2cx h2r8 h2r9)
    fun u3 ⟨rd3, wr3, cs3, _, _, hk3, hout3⟩ => ?_
  have R3 : Rep u3.mem (fb s) (stackArg s 13) V1 W2 := R2.of_keep L2.geo fun x hx => hk3 x hx
  have L3 : Lay u3 (fb s) (stackArg s 13) :=
    L2.of_rep' R2 R3 rfl (cs3 .rsp (by decide)) wr3
  have w : ∀ j, 32 < j → j < nW → W2 j = W j := fun j h hj =>
    (hW2b j hj (by omega)).trans (hW1 j hj (.inr h))
  refine ⟨L3, wr3.trans hw2, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · have hr3 : r = .r13 ∨ r = .r14 ∨ r = .r15 := by simpa using hr
    have h1 : r ∈ calleeSaved := by rcases hr3 with rfl | rfl | rfl <;> decide
    have h2 : r ∉ [Reg.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] := by rcases hr3 with rfl | rfl | rfl <;> decide
    have h3 : r ∈ [Reg.r13, .r14, .r15, .rsp] := by rcases hr3 with rfl | rfl | rfl <;> decide
    rw [cs3 r h1, k2.gpr h2, cs1 r h3, hcs r hr]
  · rw [R3.rd (d := sRbx) 41 rfl (by decide), w 41 (by decide) (by decide), h41]
  · rw [R3.rd (d := sRbp) 42 rfl (by decide), w 42 (by decide) (by decide), h42]
  · rw [R3.rd (d := sR12) 43 rfl (by decide), w 43 (by decide) (by decide), h43]
  · have hem : Spec.Rsa.bytesAt u2.mem (off (stackArg s 13) oEm) (s.gpr .rcx).toNat =
        (List.range (s.gpr .rcx).toNat).map (fun i => V1 (oEm + i)) := by
      rw [bytesAt_off]
      exact List.map_congr_left fun i hi => R2.scr _ (by have := List.mem_range.mp hi; unfold oEm oRsa; omega)
    rw [hem, List.map_congr_left (fun i hi => hV1 i (List.mem_range.mp hi)),
      bytesF_eq hM dg (by omega), bytesF_eq hM sa (by omega)] at hout3
    rw [hspec]
    exact hout3

end VG.Proof.RsaPss.X86_64
