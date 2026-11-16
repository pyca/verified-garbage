module

public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Init
public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.AbsorbCorrect
public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Common
public import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
public import VerifiedGarbage.Impl.CmacAes.Stream.X86_64.AbsorbF
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Init
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.AbsorbCorrect
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Common
meta import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
meta import VerifiedGarbage.Impl.CmacAes.Stream.X86_64.AbsorbF
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

section

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_finish`

The code copies the chaining value to `out`, computes the number of bytes held
back, and calls `vg_cmac_aes_finalize` with the state as its key and `out` as
its state: its result is the MAC of the message the state represents
(`repr_finish`). The code before the call is constant time by the taint
analysis, and the call by its own proof (`fin_rel`), its arguments pinned by
`HMid`.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (ScrSub scrSub_ok scrSub_rel)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, `out` (`O`), the scratch
pointer `S`, the rounds `R` and the writable working space `Z`: all of it
(`finishX86_64`), or all but its first 512 bytes (`finishS_wp`). -/
structure HPre (s₀ : State) (St O S : Addr) (R : Nat) (Z : Region) : Prop where
  rdi : s₀.gpr .rdi = St
  rcx : s₀.gpr .rcx = O
  r8 : s₀.gpr .r8 = S
  rsi : (s₀.gpr .rsi).toNat = R
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = []
  wr : s₀.wr = [⟨St, 304⟩, ⟨O, 16⟩, Z]
  st_o : (⟨St, 304⟩ : Region).Disjoint ⟨O, 16⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint Z
  o_s : (⟨O, 16⟩ : Region).Disjoint Z
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 304⟩
  ret_o : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨O, 16⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint Z
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint ⟨St, 304⟩
  stk_o : (below (s₀.gpr .rsp) 16).Disjoint ⟨O, 16⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint Z
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wO : O.toNat + 16 ≤ 2 ^ 64
  wZ : Z.base.toNat + Z.len ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem HPre.of {s₀ : State} (h : finishX86_64.pre s₀) :
    HPre s₀ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat ⟨s₀.gpr .r8, 2304⟩ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

/-! ## Before the call -/

theorem finishPre_ok {s₀ : State} {St O S : Addr} {R : Nat} {Z : Region} (hp : HPre s₀ St O S R Z) :
    ∃ s₁, runBlock isa finishPre s₀ = some s₁ ∧ s₁.gpr .rdi = St ∧ s₁.gpr .rsi = s₀.gpr .rsi ∧
      s₁.gpr .rdx = O ∧ s₁.gpr .rcx = St + BitVec.ofNat 64 288 ∧ s₁.gpr .r8 = s₀.gpr .rdx ∧
      s₁.gpr .r9 = S ∧ (∀ r ∈ calleeSaved, s₁.gpr r = s₀.gpr r) ∧
      s₁.zf = some (s₀.gpr .rdx == 0) ∧
      s₁.mem = copyMem s₀.mem O (St + BitVec.ofNat 64 272) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have hw := hp.wSt
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions (s₀.rd ++ s₀.wr) (St + BitVec.ofNat 64 d) 8 := by
    rw [hp.rd, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have inO (d : Nat) (hd : d + 8 ≤ 16) : InRegions s₀.wr (O + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨O, 16⟩, by simp, Offset.contains_base _ hd (by have := hp.wO; omega_arith)⟩
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, finishPre, runBlock_cons, runStep_some, runBlock_nil, at_,
      exec, readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, 
      hp.rdi, hp.rcx, inSt 272 (by decide), inSt 280 (by decide), inO 0 (by decide), inO 8 (by decide)]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, and_self, gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, 
    BitVec.and_self, hp.rdi, hp.r8]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, trivial, ?_, trivial⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [copyMem, k0, Offset.add_add]

/-- What the code before the call leaves. -/
structure HMid (s₀ : State) (St O S : Addr) (R : Nat) (Z : Region) (s : State) : Prop where
  args : FArgsZ s St O (St + BitVec.ofNat 64 288) S Z (held (s₀.gpr .rdx).toNat) R
  mem : s.mem = copyMem s₀.mem O (St + BitVec.ofNat 64 272)
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r

theorem HPre.fargs {s₀ s : State} {St O S : Addr} {R L : Nat} {Z : Region} (hp : HPre s₀ St O S R Z)
    (hL : L ≤ 16) (rdi : s.gpr .rdi = St) (rsi : s.gpr .rsi = s₀.gpr .rsi) (rdx : s.gpr .rdx = O)
    (rcx : s.gpr .rcx = St + BitVec.ofNat 64 288) (r8 : s.gpr .r8 = BitVec.ofNat 64 L)
    (r9 : s.gpr .r9 = S) (rsp : s.gpr .rsp = s₀.gpr .rsp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    FArgsZ s St O (St + BitVec.ofNat 64 288) S Z L R := by
  have hw := hp.wSt
  have pSt : Region.Sub ⟨St + BitVec.ofNat 64 288, L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_arith)
  exact
  { rdi := rdi, rdx := rdx, rcx := rcx, r8 := r8, r9 := r9
    rsi := by rw [rsi]; exact rsi_ofNat hp.rsi hp.rounds
    rounds := hp.rounds, len := hL
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    kz := hp.st_s.sub_left (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    pz := hp.st_s.sub_left pSt
    stz := hp.o_s
    stkK := by rw [rsp]; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    stkP := by rw [rsp]; exact hp.stk_st.sub_right pSt
    stkSt := by rw [rsp]; exact hp.stk_o
    stkZ := by rw [rsp]; exact hp.stk_s
    wrapK := by omega_arith
    wrapSt := hp.wO
    wrapP := by rw [toNat_add_lt St hw (by decide)]; omega_arith
    wrapZ := hp.wZ
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega_arith⟩
      · exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
    zw := by
      rw [wr, hp.wr]; exact Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; simp [hr] }

theorem finPre_wp {s₀ : State} {St O S : Addr} {R : Nat} {Z : Region} (hp : HPre s₀ St O S R Z) :
    WP isa finPre s₀ (HMid s₀ St O S R Z) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, sv₁, zf₁, m₁, rd₁, wr₁⟩ := finishPre_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := sv₁ _ (by simp [calleeSaved])
  by_cases h0 : (s₀.gpr .rdx).toNat = 0
  · refine WP.ite true (by show s₁.zf = _; rw [zf₁, beq_zero_iff, h0]; rfl)
      (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨hp.fargs (held_le _) rdi₁ rsi₁ rdx₁ rcx₁ ?_ r9₁ rsp₁ rd₁ wr₁, m₁, sv₁⟩
    rw [h0, r8₁]; exact BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  · refine WP.ite false (by show s₁.zf = _; rw [zf₁, beq_zero_iff]; simp [h0])
      (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, ite_true, r8₁, sx1, sx15]
    have hne : s₀.gpr .rdx ≠ 0 := fun e => h0 (by rw [e]; rfl)
    have hc : ∀ r ∈ calleeSaved, r ≠ .r8 := by decide
    refine ⟨hp.fargs (held_le _) rdi₁ rsi₁ rdx₁ rcx₁ (held_bv _ hne) r9₁ rsp₁ rd₁ wr₁, m₁,
      fun r hr => by simp only [gpr_setReg, gpr_arithFlags, hc r hr, ite_false]; exact sv₁ r hr⟩

/-! ## The whole function -/

/-- `finish` over the calls `T` of `vg_cmac_aes_finalize`, with the working
space `Z S`. -/
theorem finish_wpG {c : Impl.Aes.X86_64.Ctr32} {sfx : String} {Z X : Addr → Region} (T : HCall c sfx Z X)
    {s₀ : State} {St O S : Addr} {R : Nat} (hp : HPre s₀ St O S R (Z S)) :
    WP isa (finish c sfx) s₀ fun s' => gprPreserved s₀ s' ∧ finishX86_64.post s₀ s' := by
  have hw := hp.wSt
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (T.call h₁.args) fun s₂ h₂ => ?_
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := h₁.saved _ (by simp [calleeSaved])
  -- The state is unchanged before the call.
  have fSt : ∀ {d n : Nat}, d + n ≤ 304 → Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 d) n =
      Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
    rw [h₁.mem]
    exact bytesAt_frame (copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_o.sub_left (Offset.sub_base St hd)) (by omega_arith)
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], ?_⟩, ?_⟩
  · have big : Frame [⟨O, 16⟩, X S, below (s₀.gpr .rsp) 16] s₀.mem s₂.mem := by
      refine ((h₁.mem ▸ copyMem_frame _ _ _ : Frame [⟨O, 16⟩] s₀.mem s₁.mem).mono (by simp)).trans ?_
      rw [← rsp₁]; exact h₂.frame
    refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_o
    · exact hp.ret_s.sub_right (T.sub S)
    · exact Offset.base_disjoint_below _ (by decide)
  · intro key msg hr hR hc hlen
    rw [hp.rdi] at hr
    -- `St + 240` and the others, as offsets.
    rw [Proof.Cmac.Stream.repr_iff] at hr
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := hr
    have hn : (s₀.gpr .rdx).toNat = msg.length := by rw [hc, toNat_ofNat hlen]
    rw [hp.rcx]
    have hR' : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.rsi]; exact hR
    have hsch : Spec.Aes.bytesAt s₁.mem St (16 * (R + 1)) = Spec.Aes.expandKey key := by
      have := fSt (d := 0) (n := 16 * (R + 1)) (by rcases hp.rounds with h | h | h <;> omega_arith)
      rw [k0] at this; rw [this, hR']; exact hks
    have hciph : Spec.Cmac.aesWith R (Spec.Aes.bytesAt s₁.mem St (16 * (R + 1))) = Spec.Cmac.aes key := by
      rw [hsch, hR']; rfl
    have e₁ : Spec.Aes.bytesAt s₁.mem (St + 240) 32 = Spec.Aes.bytesAt s₀.mem (St + 240) 32 :=
      fSt (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + 272) 16 := by
      rw [h₁.mem]; exact copyMem_bytes _ (hp.st_o.symm.sub_right (Offset.sub_base St (by decide)))
    have e₃ : Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 288) (held (s₀.gpr .rdx).toNat) =
        Spec.Aes.bytesAt s₀.mem (St + 288) (held msg.length) := by
      rw [hn]; exact fSt (by have := held_le msg.length; omega_arith)
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish
      ((Proof.Cmac.Stream.repr_iff _ _ _ _).mpr ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩)
    have out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

theorem finish_wp (v : Ctr32Impl) {s₀ : State} (h0 : finishX86_64.pre s₀) :
    WP isa (finish v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ finishX86_64.post s₀ s' :=
  finish_wpG (HCall.base v) (HPre.of h0)

/-! ## Constant time -/

theorem finish_relG {c : Impl.Aes.X86_64.Ctr32} {sfx : String} {Z X : Addr → Region} (T : HCall c sfx Z X)
    {s₀ s₀' : State} {St O S : Addr} {R : Nat} (hp : HPre s₀ St O S R (Z S)) (hp' : HPre s₀' St O S R (Z S))
    (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) (q4 : s₀.gpr .rdx = s₀'.gpr .rdx) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finish c sfx) fun _ _ => True := by
  have q2 : s₀.gpr .rdi = s₀'.gpr .rdi := by rw [hp.rdi, hp'.rdi]
  have q3 : s₀.gpr .rsi = s₀'.gpr .rsi := BitVec.eq_of_toNat_eq (by rw [hp.rsi, hp'.rsi])
  have q5 : s₀.gpr .rcx = s₀'.gpr .rcx := by rw [hp.rcx, hp'.rcx]
  have q6 : s₀.gpr .r8 = s₀'.gpr .r8 := by rw [hp.r8, hp'.r8]
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := HMid s₀ St O S R (Z S)) (F₂ := HMid s₀' St O S R (Z S)) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩
  have c := T.rel (P := fun s₁ s₂ => HMid s₀ St O S R (Z S) s₁ ∧ HMid s₀' St O S R (Z S) s₂)
    fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.1.args, by rw [q4]; exact h.2.args, by
      rw [h.1.saved _ (by simp [calleeSaved]), h.2.saved _ (by simp [calleeSaved]), q1]⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq c

theorem finish_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : finishX86_64.pre s₀)
    (h0' : finishX86_64.pre s₀') (hq : finishX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finish v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
  have hp' : HPre s₀' (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat ⟨s₀.gpr .r8, 2304⟩ := by
    rw [q2, q3, q5, q6]; exact HPre.of h0'
  exact finish_relG (HCall.base v) (HPre.of h0) hp' q1 q4

theorem finish_ct (v : Ctr32Impl) :
    ConstantTime isa finishX86_64.pre finishX86_64.pub (finish v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finish_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Without the first 512 bytes of the working space (`finishS`) -/

/-- `finishX86_64` with a scratch buffer of 1792 bytes, for `finishS`. -/
def finishX86_64S : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 304⟩
    let out : Region := ⟨s.gpr .rcx, 16⟩
    let scr : Region := ⟨s.gpr .r8, 1792⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + 1792 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post := finishX86_64.post
  pub := finishX86_64.pub

/-- `HPre` after the `sub`, with the 1792 bytes of the scratch buffer as all
of the working space but its first 512 bytes. -/
theorem HPre.ofS {s₀ s₁ : State} (h : finishX86_64S.pre s₀) (a : ScrSub .r8 s₀ s₁) :
    HPre s₁ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8 - BitVec.ofNat 64 512) (s₀.gpr .rsi).toNat
      ⟨s₀.gpr .r8 - BitVec.ofNat 64 512 + BitVec.ofNat 64 512, 1792⟩ := by
  obtain ⟨r8₁, g₁, -, rd₁, wr₁⟩ := a
  obtain ⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o, p⟩ := h
  have eS : s₀.gpr .r8 - BitVec.ofNat 64 512 + BitVec.ofNat 64 512 = s₀.gpr .r8 := BitVec.sub_add_cancel _ _
  have sp := g₁ .rsp (by decide)
  rw [eS]
  exact ⟨g₁ _ (by decide), g₁ _ (by decide), r8₁, by rw [g₁ _ (by decide)], by rw [sp]; exact a,
    by rw [rd₁]; exact b, by rw [wr₁]; exact c, d, e, f, by rw [sp]; exact g, by rw [sp]; exact h',
    by rw [sp]; exact i, by rw [sp]; exact j, by rw [sp]; exact k, by rw [sp]; exact l, m, n, o, p⟩

theorem finishS_wp (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) {s₀ : State}
    (h0 : finishX86_64S.pre s₀) :
    WP isa (finishS v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ finishX86_64S.post s₀ s' := by
  obtain ⟨s₁, run₁, a⟩ := scrSub_ok .r8 s₀
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hp := HPre.ofS h0 a
  obtain ⟨-, g₁, m₁, -, -⟩ := a
  refine WP.mono (finish_wpG (HCall.small v f) hp) fun s' ⟨⟨hs, hr⟩, hpost⟩ => ⟨⟨fun r hr' => ?_, ?_⟩, ?_⟩
  · rw [hs r hr', g₁ r (by rintro rfl; simp [calleeSaved] at hr')]
  · rw [← g₁ .rsp (by decide), hr, m₁]
  · simp only [finishX86_64S, finishX86_64] at hpost ⊢
    rw [m₁, g₁ .rdi (by decide), g₁ .rsi (by decide), g₁ .rdx (by decide), g₁ .rcx (by decide)] at hpost
    exact hpost

theorem finishS_ct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) :
    ConstantTime isa finishX86_64S.pre finishX86_64S.pub (finishS v.callee v.suffix) := by
  intro s₀ s₀' _ _ _ _ h₁ h₂ hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
  have r : RelCT isa (fun t₁ t₂ => ∃ a b, (a = s₀ ∧ b = s₀') ∧ ScrSub .r8 a t₁ ∧ ScrSub .r8 b t₂)
      (finish v.callee v.suffix) fun _ _ => True := by
    rintro x y t t' x' y' ⟨_, _, ⟨rfl, rfl⟩, a₁, a₂⟩ ex ey
    have hp := HPre.ofS h₁ a₁
    have hp' := HPre.ofS h₂ a₂
    rw [← q2, ← q3, ← q5, ← q6] at hp'
    exact finish_relG (HCall.small v f) hp hp' (by rw [a₁.2.1 _ (by decide), a₂.2.1 _ (by decide), q1])
      (by rw [a₁.2.1 _ (by decide), a₂.2.1 _ (by decide), q4]) _ _ _ _ _ _ ⟨rfl, rfl⟩ ex ey
  exact (((scrSub_rel .r8).seq r) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Without working space for `vg_aes_ctr32` (`finishF`) -/

/-- The precondition, by name: the state `St`, `out` (`O`), the scratch
buffer `S` and the rounds `R`. -/
structure HPreF (s₀ : State) (St O S : Addr) (R : Nat) : Prop where
  rdi : s₀.gpr .rdi = St
  rcx : s₀.gpr .rcx = O
  r8 : s₀.gpr .r8 = S
  rsi : (s₀.gpr .rsi).toNat = R
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = []
  wr : s₀.wr = [⟨St, 304⟩, ⟨O, 16⟩, ⟨S, 16⟩]
  st_o : (⟨St, 304⟩ : Region).Disjoint ⟨O, 16⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 16⟩
  o_s : (⟨O, 16⟩ : Region).Disjoint ⟨S, 16⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 304⟩
  ret_o : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨O, 16⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 16⟩
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint ⟨St, 304⟩
  stk_o : (below (s₀.gpr .rsp) 16).Disjoint ⟨O, 16⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint ⟨S, 16⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wO : O.toNat + 16 ≤ 2 ^ 64
  wS : S.toNat + 16 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem HPreF.of {s₀ : State} (h : finishX86_64F.pre s₀) :
    HPreF s₀ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

/-! ## Before the call -/

theorem finishPreF_ok {s₀ : State} {St O S : Addr} {R : Nat} (hp : HPreF s₀ St O S R) :
    ∃ s₁, runBlock isa finishPreF s₀ = some s₁ ∧ s₁.gpr .rdi = St ∧ s₁.gpr .rsi = s₀.gpr .rsi ∧
      s₁.gpr .rdx = O ∧ s₁.gpr .rcx = St + BitVec.ofNat 64 288 ∧ s₁.gpr .r8 = s₀.gpr .rdx ∧
      s₁.gpr .r9 = S - BitVec.ofNat 64 2048 ∧ (∀ r ∈ calleeSaved, s₁.gpr r = s₀.gpr r) ∧
      s₁.zf = some (s₀.gpr .rdx == 0) ∧
      s₁.mem = copyMem s₀.mem O (St + BitVec.ofNat 64 272) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have hw := hp.wSt
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions (s₀.rd ++ s₀.wr) (St + BitVec.ofNat 64 d) 8 := by
    rw [hp.rd, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have inO (d : Nat) (hd : d + 8 ≤ 16) : InRegions s₀.wr (O + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨O, 16⟩, by simp, Offset.contains_base _ hd (by have := hp.wO; omega_arith)⟩
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, finishPreF, runBlock_cons, runStep_some, runBlock_nil, at_,
      exec, readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, 
      hp.rdi, hp.rcx, inSt 272 (by decide), inSt 280 (by decide), inO 0 (by decide), inO 8 (by decide)]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, and_self, gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, 
    BitVec.and_self, hp.rdi, hp.r8]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, trivial, ?_, trivial⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [copyMem, k0, Offset.add_add]

/-- What the code before the call leaves. -/
structure HMidF (s₀ : State) (St O S : Addr) (R : Nat) (s : State) : Prop where
  args : FArgsF s St O (St + BitVec.ofNat 64 288) (S - BitVec.ofNat 64 2048) (held (s₀.gpr .rdx).toNat) R
  mem : s.mem = copyMem s₀.mem O (St + BitVec.ofNat 64 272)
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r

theorem HPreF.fargs {s₀ s : State} {St O S : Addr} {R L : Nat} (hp : HPreF s₀ St O S R) (hL : L ≤ 16)
    (rdi : s.gpr .rdi = St) (rsi : s.gpr .rsi = s₀.gpr .rsi) (rdx : s.gpr .rdx = O)
    (rcx : s.gpr .rcx = St + BitVec.ofNat 64 288) (r8 : s.gpr .r8 = BitVec.ofNat 64 L)
    (r9 : s.gpr .r9 = S - BitVec.ofNat 64 2048) (rsp : s.gpr .rsp = s₀.gpr .rsp) (rd : s.rd = s₀.rd)
    (wr : s.wr = s₀.wr) :
    FArgsF s St O (St + BitVec.ofNat 64 288) (S - BitVec.ofNat 64 2048) L R := by
  have hw := hp.wSt
  have e : S - BitVec.ofNat 64 2048 + BitVec.ofNat 64 2048 = S := BitVec.sub_add_cancel _ _
  have pSt : Region.Sub ⟨St + BitVec.ofNat 64 288, L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_arith)
  exact
  { rdi := rdi, rdx := rdx, rcx := rcx, r8 := r8, r9 := r9
    rsi := by rw [rsi]; exact rsi_ofNat hp.rsi hp.rounds
    rounds := hp.rounds, len := hL
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := by rw [e]; exact hp.st_s.sub_left (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := by rw [e]; exact hp.st_s.sub_left pSt
    sts := by rw [e]; exact hp.o_s
    stkK := by rw [rsp]; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    stkP := by rw [rsp]; exact hp.stk_st.sub_right pSt
    stkSt := by rw [rsp]; exact hp.stk_o
    stkS := by rw [rsp, e]; exact hp.stk_s
    wrapK := by omega_arith
    wrapSt := hp.wO
    wrapP := by rw [toNat_add_lt St hw (by decide)]; omega_arith
    wrapS := by rw [e]; exact hp.wS
    reads := by
      rw [rd, wr, hp.rd, hp.wr, e]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega_arith⟩
      · exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 16⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr, hp.wr, e]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 16⟩, by simp, 0, by simp, by simp⟩ }

theorem finPreF_wp {s₀ : State} {St O S : Addr} {R : Nat} (hp : HPreF s₀ St O S R) :
    WP isa finPreF s₀ (HMidF s₀ St O S R) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, sv₁, zf₁, m₁, rd₁, wr₁⟩ := finishPreF_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := sv₁ _ (by simp [calleeSaved])
  by_cases h0 : (s₀.gpr .rdx).toNat = 0
  · refine WP.ite true (by show s₁.zf = _; rw [zf₁, beq_zero_iff, h0]; rfl)
      (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨hp.fargs (held_le _) rdi₁ rsi₁ rdx₁ rcx₁ ?_ r9₁ rsp₁ rd₁ wr₁, m₁, sv₁⟩
    rw [h0, r8₁]; exact BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  · refine WP.ite false (by show s₁.zf = _; rw [zf₁, beq_zero_iff]; simp [h0])
      (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, ite_true, r8₁, sx1, sx15]
    have hne : s₀.gpr .rdx ≠ 0 := fun e => h0 (by rw [e]; rfl)
    have hc : ∀ r ∈ calleeSaved, r ≠ .r8 := by decide
    refine ⟨hp.fargs (held_le _) rdi₁ rsi₁ rdx₁ rcx₁ (held_bv _ hne) r9₁ rsp₁ rd₁ wr₁, m₁,
      fun r hr => by simp only [gpr_setReg, gpr_arithFlags, hc r hr, ite_false]; exact sv₁ r hr⟩

/-! ## The whole function -/

/-- `finish_wp`, over an implementation of `vg_aes_ctr32` that needs no
working space. -/
theorem finishF_wp (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) {s₀ : State}
    (h0 : finishX86_64F.pre s₀) :
    WP isa (finishF v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ finishX86_64F.post s₀ s' := by
  have hp := HPreF.of h0
  generalize s₀.gpr .rdi = St at hp
  generalize s₀.gpr .rcx = O at hp
  generalize s₀.gpr .r8 = S at hp
  generalize (s₀.gpr .rsi).toNat = R at hp
  have hw := hp.wSt
  refine WP.seq (WP.mono (finPreF_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (fin_callF v f _ h₁.args) fun s₂ h₂ => ?_
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := h₁.saved _ (by simp [calleeSaved])
  -- The state is unchanged before the call.
  have fSt : ∀ {d n : Nat}, d + n ≤ 304 → Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 d) n =
      Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
    rw [h₁.mem]
    exact bytesAt_frame (copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_o.sub_left (Offset.sub_base St hd)) (by omega_arith)
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], ?_⟩, ?_⟩
  · have big : Frame [⟨O, 16⟩, ⟨S, 16⟩, below (s₀.gpr .rsp) 16] s₀.mem s₂.mem := by
      refine ((h₁.mem ▸ copyMem_frame _ _ _ : Frame [⟨O, 16⟩] s₀.mem s₁.mem).mono (by simp)).trans ?_
      have := h₂.frame
      rw [BitVec.sub_add_cancel] at this
      rw [← rsp₁]; exact this
    refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_o
    · exact hp.ret_s
    · exact Offset.base_disjoint_below _ (by decide)
  · intro key msg hr hR hc hlen
    rw [hp.rdi] at hr
    -- `St + 240` and the others, as offsets.
    rw [Proof.Cmac.Stream.repr_iff] at hr
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := hr
    have hn : (s₀.gpr .rdx).toNat = msg.length := by rw [hc, toNat_ofNat hlen]
    rw [hp.rcx]
    have hR' : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.rsi]; exact hR
    have hsch : Spec.Aes.bytesAt s₁.mem St (16 * (R + 1)) = Spec.Aes.expandKey key := by
      have := fSt (d := 0) (n := 16 * (R + 1)) (by rcases hp.rounds with h | h | h <;> omega_arith)
      rw [k0] at this; rw [this, hR']; exact hks
    have hciph : Spec.Cmac.aesWith R (Spec.Aes.bytesAt s₁.mem St (16 * (R + 1))) = Spec.Cmac.aes key := by
      rw [hsch, hR']; rfl
    have e₁ : Spec.Aes.bytesAt s₁.mem (St + 240) 32 = Spec.Aes.bytesAt s₀.mem (St + 240) 32 :=
      fSt (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + 272) 16 := by
      rw [h₁.mem]; exact copyMem_bytes _ (hp.st_o.symm.sub_right (Offset.sub_base St (by decide)))
    have e₃ : Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 288) (held (s₀.gpr .rdx).toNat) =
        Spec.Aes.bytesAt s₀.mem (St + 288) (held msg.length) := by
      rw [hn]; exact fSt (by have := held_le msg.length; omega_arith)
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish
      ((Proof.Cmac.Stream.repr_iff _ _ _ _).mpr ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩)
    have out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

/-! ## Constant time -/

theorem finishF_rel (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) {s₀ s₀' : State}
    (h0 : finishX86_64F.pre s₀) (h0' : finishX86_64F.pre s₀') (hq : finishX86_64F.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finishF v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
  have hp := HPreF.of h0
  have hp' : HPreF s₀' (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat := by
    rw [q2, q3, q5, q6]; exact HPreF.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) finPreF h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := HMidF s₀ _ _ _ _) (F₂ := HMidF s₀' _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finPreF_wp hp, finPreF_wp hp'⟩
  have c := fin_relF v f ("vg_cmac_aes_finalize" ++ v.suffix) (P := fun s₁ s₂ =>
      HMidF s₀ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat s₁ ∧
      HMidF s₀' (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat s₂)
    fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.1.args, by rw [q4]; exact h.2.args, by
      rw [h.1.saved _ (by simp [calleeSaved]), h.2.saved _ (by simp [calleeSaved]), q1]⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq c

theorem finishF_ct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    ConstantTime isa finishX86_64F.pre finishX86_64F.pub (finishF v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finishF_rel v f h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86_64

end

section

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb` is constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the registers the correctness proof pins to values of the public arguments
(`AMid₁`, `AAfter₁`, `AMid₂`, `AAfter₂`), and each call of
`vg_cmac_aes_update` is constant time by its own proof (`upd_rel`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

/-- What the first call leaves, for `chain2`. -/
structure AAfter₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem call1_after {u : Impl.CmacAes.X86_64.Update} {Zf Xf : Addr → Region} (hcall : ACall u Zf Xf)
    {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₁ s₀ St D S (Zf S) L R s) :
    WP isa (.call u.name u.code) s
      (AAfter₁ s₀ St D S L) :=
  WP.mono (hcall.call h.args) fun _ h₆ =>
    ⟨by rw [h₆.saved _ (by simp [calleeSaved]), h.rbx], by rw [h₆.saved _ (by simp [calleeSaved]), h.rbp],
      by rw [h₆.saved _ (by simp [calleeSaved]), h.r13], by rw [h₆.saved _ (by simp [calleeSaved]), h.r14],
      by rw [h₆.saved _ (by simp [calleeSaved]), h.r15], by rw [h₆.saved _ (by simp [calleeSaved]), h.rsp],
      by rw [h₆.rd, h.rd], by rw [h₆.wr, h.wr]⟩

/-- What `chain2` leaves, for the second call. -/
structure AMid₂ (s₀ : State) (St D S : Addr) (Z : Region) (L R : Nat) (s : State) : Prop where
  args : UArgsZ s St (St + BitVec.ofNat 64 272) (D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)) S Z R
    (nbOf (s₀.gpr .rdx).toNat L)
  rbx : s.gpr .rbx = St
  r12 : s.gpr .r12 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .rdx).toNat L)
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem chain2_mid {s₀ s : State} {St D S : Addr} {Z : Region} {L R : Nat} (hp : APre s₀ St D S Z L R)
    (h : AAfter₁ s₀ St D S L s) : WP isa chain2 s (AMid₂ s₀ St D S Z L R) := by
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .rdx).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have ⟨hfL, _⟩ := f_le c L
  have hsum := nb_le c L
  obtain ⟨rbx₆, rbp₆, r13₆, r14₆, r15₆, rsp₆, rd₆, wr₆⟩ := h
  rw [hc] at r13₆ r14₆
  refine WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_arith) r14₆) fun s₇ h₇ => ?_
  obtain ⟨r12₇, r8₇, rdi₇, rsi₇, rdx₇, rcx₇, r9₇, sv₇, -, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at r12₇ r8₇
  have k₇ (r : Reg) (hr : r ∈ calleeSaved) (a : r ≠ .r12) : s₇.gpr r = s.gpr r := sv₇ r hr a
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  subst hc
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L), 16 * nbOf (s₀.gpr .rdx).toNat L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_arith)
  refine ⟨hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)) (n := nbOf (s₀.gpr .rdx).toNat L)
    (by rw [rdi₇, rbx₆]) (by rw [rsi₇, rbp₆]) (by rw [rdx₇, rbx₆]) (by rw [rcx₇, r13₆]) r8₇
    (by rw [r9₇, r15₆]) (by rw [k₇ _ (by simp [calleeSaved]) (by decide), rsp₆]) (by rw [rd₇, rd₆])
    (by rw [wr₇, wr₆]) (by omega_arith) ((hp.st_d.sub_left c272).symm.sub_left dD)
    (hp.d_s.sub_left dD) (hp.stk_d.sub_right dD)
    (by
      by_cases h0 : nbOf (s₀.gpr .rdx).toNat L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)).isLt; omega_arith
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_arith)
    ⟨⟨D, L⟩, by simp, fOf (s₀.gpr .rdx).toNat L, rfl, by simp; omega_arith⟩,
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), rbx₆], r12₇,
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), r13₆], by rw [k₇ _ (by simp [calleeSaved]) (by decide), r14₆],
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), r15₆],
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), rsp₆]⟩

/-- What the second call leaves, for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = St
  r12 : s.gpr .r12 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .rdx).toNat L)
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S

theorem call2_after {u : Impl.CmacAes.X86_64.Update} {Zf Xf : Addr → Region} (hcall : ACall u Zf Xf)
    {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₂ s₀ St D S (Zf S) L R s) :
    WP isa (.call u.name u.code) s
      (AAfter₂ s₀ St D S L) :=
  WP.mono (hcall.call h.args) fun _ h₈ =>
    ⟨by rw [h₈.saved _ (by simp [calleeSaved]), h.rbx], by rw [h₈.saved _ (by simp [calleeSaved]), h.r12],
      by rw [h₈.saved _ (by simp [calleeSaved]), h.r13], by rw [h₈.saved _ (by simp [calleeSaved]), h.r14],
      by rw [h₈.saved _ (by simp [calleeSaved]), h.r15]⟩

/-- `absorb` over the calls `hcall` is constant time, for runs from two
states with the same public arguments. -/
theorem absorb_relG {u : Impl.CmacAes.X86_64.Update} {Zf Xf : Addr → Region} (hcall : ACall u Zf Xf)
    {s₀ s₀' : State} {St D S : Addr} {L R : Nat}
    (hp : APre s₀ St D S (Zf S) L R) (hp' : APre s₀' St D S (Zf S) L R)
    (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) (q3 : s₀.gpr .rsi = s₀'.gpr .rsi) (q4 : s₀.gpr .rdx = s₀'.gpr .rdx) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (absorb u) fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) absorbPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r13, .r14, .r15, .rsp]) chain2 h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .r12, .r13, .r14, .r15]) absorbPost h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hp.rdi, hp'.rdi]
      · exact q3
      · exact q4
      · rw [hp.rcx, hp'.rcx]
      · rw [hp.r8', hp'.r8']
      · rw [hp.r9, hp'.r9]
      · exact q1) hA).wp
    (F₁ := AMid₁ s₀ St D S (Zf S) L R) (F₂ := AMid₁ s₀' St D S (Zf S) L R) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨absorbPre_wp hp, absorbPre_wp hp'⟩
  have c₁ := (hcall.rel (P := fun a b => AMid₁ s₀ St D S (Zf S) L R a ∧ AMid₁ s₀' St D S (Zf S) L R b)
    fun a b h => ⟨_, _, _, _, _, _, h.1.args, by rw [q4]; exact h.2.args, by rw [h.1.rsp, h.2.rsp, q1]⟩).wp
    (F₁ := AAfter₁ s₀ St D S L) (F₂ := AAfter₁ s₀' St D S L) fun a b h =>
      ⟨call1_after hcall h.1, call1_after hcall h.2⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => AAfter₁ s₀ St D S L a ∧ AAfter₁ s₀' St D S L b) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h.1.rbx, h.2.rbx]
      · rw [h.1.rbp, h.2.rbp, q3]
      · rw [h.1.r13, h.2.r13, q4]
      · rw [h.1.r14, h.2.r14, q4]
      · rw [h.1.r15, h.2.r15]
      · rw [h.1.rsp, h.2.rsp, q1]) hB).wp
    (F₁ := AMid₂ s₀ St D S (Zf S) L R) (F₂ := AMid₂ s₀' St D S (Zf S) L R) fun a b h =>
      ⟨chain2_mid hp h.1, chain2_mid hp' h.2⟩
  have c₂ := (hcall.rel (P := fun a b => AMid₂ s₀ St D S (Zf S) L R a ∧ AMid₂ s₀' St D S (Zf S) L R b)
    fun a b h => ⟨_, _, _, _, _, _, h.1.args, by rw [q4]; exact h.2.args, by rw [h.1.rsp, h.2.rsp, q1]⟩).wp
    (F₁ := AAfter₂ s₀ St D S L) (F₂ := AAfter₂ s₀' St D S L) fun a b h =>
      ⟨call2_after hcall h.1, call2_after hcall h.2⟩
  have p := RelCT.taint (A := taint) (P := fun a b => AAfter₂ s₀ St D S L a ∧ AAfter₂ s₀' St D S L b) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.rbx, h.2.rbx]
      · rw [h.1.r12, h.2.r12, q4]
      · rw [h.1.r13, h.2.r13, q4]
      · rw [h.1.r14, h.2.r14, q4]
      · rw [h.1.r15, h.2.r15]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem absorb_rel (v : UpdateImpl) {s₀ s₀' : State} (h0 : absorbX86_64.pre s₀) (h0' : absorbX86_64.pre s₀')
    (hq : absorbX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (absorb v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp' : APre s₀' (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r9) ⟨s₀.gpr .r9, 2304⟩ (s₀.gpr .r8).toNat
      (s₀.gpr .rsi).toNat := by
    rw [q2, q3, q5, q6, q7]; exact APre.of h0'
  exact absorb_relG (ACall.base v) (APre.of h0) hp' q1 q3 q4

theorem absorb_ct (v : UpdateImpl) :
    ConstantTime isa absorbX86_64.pre absorbX86_64.pub (absorb v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86_64

end

/-!
# Streaming AES-CMAC on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of AES), a state
satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with 16 bytes of stack: the return addresses of the
call of a CMAC function and of its call of `vg_aes_ctr32`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl subkeys_mx finalize_mx subkeys_spSafe finalize_spSafe)

theorem init_mx (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, Code.allInstrs,
    ekCall_allInstrs (p := fun i => !loadsMxcsr i) (fun _ => rfl) v.expandMxcsr, subkeys_mx v]
  decide +kernel

theorem absorb_mx (v : UpdateImpl) : (absorb v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [absorb, absorbPre, absorbPost, held, fill, copy, chain1, chain2, Code.allInstrs, v.mxcsr]
  decide +kernel

theorem finish_mx (v : Ctr32Impl) : (finish v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [finish, finPre, lastLen, Code.allInstrs, finalize_mx v]; decide +kernel

theorem init_spSafe (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, Code.all,
    ekCall_all (p := fun i => !X86_64.isa.writesSp i) (fun _ => rfl) v.expandSpSafe, subkeys_spSafe v]
  decide +kernel

theorem absorb_spSafe (v : UpdateImpl) :
    (absorb v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [absorb, absorbPre, absorbPost, held, fill, copy, chain1, chain2, Code.all, v.spSafe]
  decide +kernel

theorem finish_spSafe (v : Ctr32Impl) :
    (finish v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [finish, finPre, lastLen, Code.all, finalize_spSafe v]; decide +kernel

theorem init_correct (v : Ctr32Impl) (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa (init v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (init_mx v) he hg, hp⟩

theorem absorb_correct (v : UpdateImpl) (s : State) (hs : absorbX86_64.pre s) :
    ∃ t s', Exec isa (absorb v.callee) s t s' ∧ abiPreserved s s' ∧ absorbX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := absorb_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (absorb_mx v) he hg, hp⟩

theorem finish_correct (v : Ctr32Impl) (s : State) (hs : finishX86_64.pre s) :
    ∃ t s', Exec isa (finish v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ finishX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finish_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (finish_mx v) he hg, hp⟩

theorem initF_mx (v : Ctr32Impl) :
    (initF ekF v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h : ekF.code.allInstrs (fun i => !loadsMxcsr i) = true := Ctr32Impl.aesni.expandMxcsr
  simp only [initF, init, Code.allInstrs,
    ekCall_allInstrs (p := fun i => !loadsMxcsr i) (fun _ => rfl) h, subkeys_mx v]
  decide +kernel

theorem initF_spSafe (v : Ctr32Impl) :
    (initF ekF v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h : ekF.code.all (fun i => !X86_64.isa.writesSp i) = true := Ctr32Impl.aesni.expandSpSafe
  simp only [initF, init, Code.all,
    ekCall_all (p := fun i => !X86_64.isa.writesSp i) (fun _ => rfl) h, subkeys_spSafe v]
  decide +kernel

theorem initF_correct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) (s : State)
    (hs : initX86_64F.pre s) :
    ∃ t s', Exec isa (initF ekF v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initX86_64F.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := initF_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (initF_mx v) he hg, hp⟩

theorem finishF_mx (v : Ctr32Impl) : (finishF v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [finishF, finPreF, lastLen, Code.allInstrs, finalize_mx v]; decide +kernel

theorem finishF_spSafe (v : Ctr32Impl) :
    (finishF v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [finishF, finPreF, lastLen, Code.all, finalize_spSafe v]; decide +kernel

theorem finishF_correct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) (s : State)
    (hs : finishX86_64F.pre s) :
    ∃ t s', Exec isa (finishF v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ finishX86_64F.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finishF_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (finishF_mx v) he hg, hp⟩

/-- A state satisfying `vg_cmac_aes_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 16 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem init_verified (v : Ctr32Impl) :
    Verified X86_64.target (init v.expand v.callee v.suffix) (initScratchContract X86_64.abi 16) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [initScratchContract, initScratchSig, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost, initX86_64, X86_64.abi,
      X86_64.argRegs] [initSat] using initSat)

/-- `vg_cmac_aes_init` with `scratch: *mut [u64; 19]`, for `initF`. -/
def initScratchSigF : Sig where
  params := [("state", .array true .u64 38), ("key", .slice false .u8 "key_len"),
    ("scratch", .array true .u64 19)]

/-- `aesInitContract`, whatever `scratch` is (of 19 words). -/
def initScratchContractF {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSigF.contract A
    (pre := fun state key keyLen _scratch => Spec.Cmac.aesInitPre A.ptrBits state key keyLen)
    (post := fun state key keyLen _scratch => Spec.Cmac.aesInitPost A.ptrBits state key keyLen)
    (stack := stack)

/-- A state satisfying `vg_cmac_aes_init`'s precondition, with 152 bytes of
working space. -/
def initSatF : State := { initSat with wr := [⟨0x1000, 304⟩, ⟨0x4000, 152⟩] }

theorem initF_verified (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    Verified X86_64.target (initF ekF v.callee v.suffix) (initScratchContractF X86_64.abi 16) :=
  Verified.of_correct (initF_correct v f) (initF_ct v f) (by
    sig_implies [initScratchContractF, initScratchSigF, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost,
      initX86_64F, initX86_64, X86_64.abi, X86_64.argRegs] [initSatF, initSat] using initSatF)

theorem initS_mx (v : Ctr32Impl) :
    (initS v.expand v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [initS, Code.allInstrs, init_mx v]; decide +kernel

theorem initS_spSafe (v : Ctr32Impl) :
    (initS v.expand v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [initS, Code.all, init_spSafe v]; decide +kernel

theorem initS_correct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) (s : State)
    (hs : initX86_64S.pre s) :
    ∃ t s', Exec isa (initS v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧
      initX86_64S.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := initS_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (initS_mx v) he hg, hp⟩

/-- `vg_cmac_aes_init` with `scratch: *mut [u64; 224]`, for `initS`. -/
def initScratchSigS : Sig where
  params := [("state", .array true .u64 38), ("key", .slice false .u8 "key_len"),
    ("scratch", .array true .u64 224)]

/-- `aesInitContract`, whatever `scratch` is (of 224 words). -/
def initScratchContractS {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSigS.contract A
    (pre := fun state key keyLen _scratch => Spec.Cmac.aesInitPre A.ptrBits state key keyLen)
    (post := fun state key keyLen _scratch => Spec.Cmac.aesInitPost A.ptrBits state key keyLen)
    (stack := stack)

/-- A state satisfying `vg_cmac_aes_init`'s precondition, with 1792 bytes of
working space. -/
def initSatS : State := { initSat with wr := [⟨0x1000, 304⟩, ⟨0x4000, 1792⟩] }

theorem initS_verified (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) :
    Verified X86_64.target (initS v.expand v.callee v.suffix) (initScratchContractS X86_64.abi 16) :=
  Verified.of_correct (initS_correct v f) (initS_ct v f) (by
    sig_implies [initScratchContractS, initScratchSigS, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost,
      initX86_64S, initX86_64, X86_64.abi, X86_64.argRegs] [initSatS, initSat] using initSatS)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem absorb_verified (v : UpdateImpl) :
    Verified X86_64.target (absorb v.callee) (absorbScratchContract X86_64.abi 16) :=
  Verified.of_correct (absorb_correct v) (absorb_ct v) (by
    sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost, absorbX86_64, X86_64.abi,
      X86_64.argRegs] [absorbSat] using absorbSat)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rcx => 0x2000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 2304⟩]

theorem finish_verified (v : Ctr32Impl) :
    Verified X86_64.target (finish v.callee v.suffix) (finishScratchContract X86_64.abi 16) :=
  Verified.of_correct (finish_correct v) (finish_ct v) (by
    sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost, finishX86_64, X86_64.abi,
      X86_64.argRegs] [finishSat] using finishSat)

theorem finishS_mx (v : Ctr32Impl) :
    (finishS v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [finishS, Code.allInstrs, finish_mx v]; decide +kernel

theorem finishS_spSafe (v : Ctr32Impl) :
    (finishS v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [finishS, Code.all, finish_spSafe v]; decide +kernel

theorem finishS_correct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) (s : State)
    (hs : finishX86_64S.pre s) :
    ∃ t s', Exec isa (finishS v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ finishX86_64S.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finishS_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (finishS_mx v) he hg, hp⟩

/-- `vg_cmac_aes_finish` with `scratch: *mut [u64; 224]`, for `finishS`. -/
def finishScratchSigS : Sig where
  params := [("state", .array true .u64 38), ("rounds", .int .usize true),
    ("count", .int .u64 true), ("out", .array true .u8 16),
    ("scratch", .array true .u64 224)]

/-- `aesFinishContract`, whatever `scratch` is (of 224 words). -/
def finishScratchContractS {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finishScratchSigS.contract A
    (pre := fun state rounds count out _scratch => Spec.Cmac.aesFinishPre A.ptrBits state rounds count out)
    (post := fun state rounds count out _scratch => Spec.Cmac.aesFinishPost A.ptrBits state rounds count out)
    (stack := stack)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, with 1792 bytes
of working space. -/
def finishSatS : State := { finishSat with wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 1792⟩] }

theorem finishS_verified (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) :
    Verified X86_64.target (finishS v.callee v.suffix) (finishScratchContractS X86_64.abi 16) :=
  Verified.of_correct (finishS_correct v f) (finishS_ct v f) (by
    sig_implies [finishScratchContractS, finishScratchSigS, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost,
      finishX86_64S, finishX86_64, X86_64.abi, X86_64.argRegs] [finishSatS, finishSat] using finishSatS)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, with 16 bytes of
working space. -/
def finishSatF : State := { finishSat with wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 16⟩] }

theorem finishF_verified (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    Verified X86_64.target (finishF v.callee v.suffix) (finishScratchContractF X86_64.abi 16) :=
  Verified.of_correct (finishF_correct v f) (finishF_ct v f) (by
    sig_implies [finishScratchContractF, finishScratchSigF, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost,
      finishX86_64F, finishX86_64, X86_64.abi, X86_64.argRegs] [finishSatF, finishSat] using finishSatF)

end VG.Proof.CmacAes.Stream.X86_64

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb` without working space

Over an implementation of `vg_cmac_aes_update` that never touches its
scratch buffer (`UpdateFree`), `absorbF` is given `scratch - 2176`, so its
own scratch buffer is only the 48 bytes of the registers it saves
(`absorbX86_64F`): the proof is `absorb`'s over those calls
(`ACall.free`), after the `sub`.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.CmacAes.X86_64 (UpdateImpl UpdateFree)

/-- `absorbX86_64` with a scratch buffer of 48 bytes, for `absorbF`. -/
def absorbX86_64F : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 304⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 48⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 48 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post := absorbX86_64.post
  pub := absorbX86_64.pub

/-- The `sub` before `absorb`. -/
theorem subA_ok (s₀ : State) :
    ∃ s₁, runBlock isa [.alu .sub .r9 (.imm (BitVec.ofNat 32 2176))] s₀ = some s₁ ∧
      s₁.gpr .r9 = s₀.gpr .r9 - BitVec.ofNat 64 2176 ∧ (∀ r, r ≠ .r9 → s₁.gpr r = s₀.gpr r) ∧
      s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  refine ⟨_, by simp only [runBlock_cons, exec, readSrc, execAlu]; rfl, ?_⟩
  simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ↓reduceIte]
  exact ⟨by rw [show BitVec.signExtend 64 (BitVec.ofNat 32 2176) = BitVec.ofNat 64 2176 by decide],
    fun r h => by simp [h], trivial, trivial, trivial⟩

/-- `APre` after the `sub`, with the 48 bytes of the scratch buffer as the
working space. -/
theorem APre.ofF {s₀ s₁ : State} (h : absorbX86_64F.pre s₀)
    (r9₁ : s₁.gpr .r9 = s₀.gpr .r9 - BitVec.ofNat 64 2176) (g₁ : ∀ r, r ≠ .r9 → s₁.gpr r = s₀.gpr r)
    (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr) :
    APre s₁ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r9 - BitVec.ofNat 64 2176)
      ⟨s₀.gpr .r9 - BitVec.ofNat 64 2176 + BitVec.ofNat 64 2176, 48⟩ (s₀.gpr .r8).toNat
      (s₀.gpr .rsi).toNat := by
  obtain ⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o, p⟩ := h
  have eS : s₀.gpr .r9 - BitVec.ofNat 64 2176 + BitVec.ofNat 64 2176 = s₀.gpr .r9 := BitVec.sub_add_cancel _ _
  have sp := g₁ .rsp (by decide)
  rw [eS]
  exact ⟨g₁ _ (by decide), g₁ _ (by decide), by rw [g₁ _ (by decide)], r9₁, by rw [g₁ _ (by decide)],
    by rw [sp]; exact a, by rw [rd₁]; exact b, by rw [wr₁]; exact c, d, e, f, by rw [sp]; exact g,
    by rw [sp]; exact h', by rw [sp]; exact i, by rw [sp]; exact j, by rw [sp]; exact k, by rw [sp]; exact l,
    m, n, o, p, ⟨0, by rw [eS, BitVec.add_zero], by simp⟩⟩

theorem absorbF_wp (v : UpdateImpl) (f : UpdateFree v.callee) {s₀ : State} (h0 : absorbX86_64F.pre s₀) :
    WP isa (absorbF v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ absorbX86_64F.post s₀ s' := by
  obtain ⟨s₁, run₁, r9₁, g₁, m₁, rd₁, wr₁⟩ := subA_ok s₀
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hp := APre.ofF h0 r9₁ g₁ rd₁ wr₁
  refine WP.mono (absorb_wpG (ACall.free v f) hp) fun s' ⟨⟨hs, hr⟩, hpost⟩ => ⟨⟨fun r hr' => ?_, ?_⟩, ?_⟩
  · rw [hs r hr', g₁ r (by rintro rfl; simp [calleeSaved] at hr')]
  · rw [← g₁ .rsp (by decide), hr, m₁]
  · simp only [absorbX86_64F, absorbX86_64] at hpost ⊢
    rw [m₁, g₁ .rdi (by decide), g₁ .rsi (by decide), g₁ .rdx (by decide), g₁ .rcx (by decide),
      g₁ .r8 (by decide)] at hpost
    exact hpost

/-- What the `sub` before `absorb` leaves. -/
def SubA (s₀ s : State) : Prop :=
  s.gpr .r9 = s₀.gpr .r9 - BitVec.ofNat 64 2176 ∧ (∀ r, r ≠ .r9 → s.gpr r = s₀.gpr r) ∧
    s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

theorem absorbF_ct (v : UpdateImpl) (f : UpdateFree v.callee) :
    ConstantTime isa absorbX86_64F.pre absorbX86_64F.pub (absorbF v.callee) := by
  intro s₀ s₀' _ _ _ _ h₁ h₂ hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block [.alu .sub .r9 (.imm (BitVec.ofNat 32 2176))]) h).isSome = true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := SubA s₀) (F₂ := SubA s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, r, h⟩ := subA_ok a
      obtain ⟨_, r', h'⟩ := subA_ok b
      exact ⟨WP.of_runBlock ⟨_, r, h⟩, WP.of_runBlock ⟨_, r', h'⟩⟩
  have r : RelCT isa (fun a b => SubA s₀ a ∧ SubA s₀' b) (absorb v.callee) fun _ _ => True := by
    intro x y t t' x' y' ⟨⟨r9₁, g₁, _, rd₁, wr₁⟩, ⟨r9₂, g₂, _, rd₂, wr₂⟩⟩ ex ey
    have hp := APre.ofF h₁ r9₁ g₁ rd₁ wr₁
    have hp' := APre.ofF h₂ r9₂ g₂ rd₂ wr₂
    rw [← q2, ← q5, ← q6, ← q7, ← q3] at hp'
    exact absorb_relG (ACall.free v f) hp hp' (by rw [g₁ _ (by decide), g₂ _ (by decide), q1])
      (by rw [g₁ _ (by decide), g₂ _ (by decide), q3]) (by rw [g₁ _ (by decide), g₂ _ (by decide), q4])
      _ _ _ _ _ _ ⟨rfl, rfl⟩ ex ey
  exact ((a.mono (fun _ _ h => h) fun _ _ h => h.2).seq r _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem absorbF_mx (v : UpdateImpl) : (absorbF v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [absorbF, Code.allInstrs, absorb_mx v]; decide +kernel

theorem absorbF_spSafe (v : UpdateImpl) :
    (absorbF v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [absorbF, Code.all, absorb_spSafe v]; decide +kernel

theorem absorbF_correct (v : UpdateImpl) (f : UpdateFree v.callee) (s : State) (hs : absorbX86_64F.pre s) :
    ∃ t s', Exec isa (absorbF v.callee) s t s' ∧ abiPreserved s s' ∧ absorbX86_64F.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := absorbF_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (absorbF_mx v) he hg, hp⟩

/-- `vg_cmac_aes_absorb` with `scratch: *mut [u64; 6]`, for `absorbF`. -/
def absorbScratchSigF : Sig where
  params := [("state", .array true .u64 38), ("rounds", .int .usize true),
    ("count", .int .u64 true), ("data", .slice false .u8 "len"),
    ("scratch", .array true .u64 6)]

/-- `aesAbsorbContract`, whatever `scratch` is (of 6 words). -/
def absorbScratchContractF {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  absorbScratchSigF.contract A
    (pre := fun state rounds count data len _scratch =>
      Spec.Cmac.aesAbsorbPre A.ptrBits state rounds count data len)
    (post := fun state rounds count data len _scratch =>
      Spec.Cmac.aesAbsorbPost A.ptrBits state rounds count data len)
    (stack := stack)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, with 48 bytes of
working space. -/
def absorbSatF : State := { absorbSat with wr := [⟨0x1000, 304⟩, ⟨0x4000, 48⟩] }

theorem absorbF_verified (v : UpdateImpl) (f : UpdateFree v.callee) :
    Verified X86_64.target (absorbF v.callee) (absorbScratchContractF X86_64.abi 16) :=
  Verified.of_correct (absorbF_correct v f) (absorbF_ct v f) (by
    sig_implies [absorbScratchContractF, absorbScratchSigF, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost,
      absorbX86_64F, absorbX86_64, X86_64.abi, X86_64.argRegs] [absorbSatF, absorbSat] using absorbSatF)

/-! ## `vg_cmac_aes_absorb` without the first 512 bytes of the working space

Over an implementation of `vg_cmac_aes_update` that never touches the first
512 bytes of its scratch buffer (`UpdateSmall`), `absorbS` is given
`scratch - 512`, so its own scratch buffer is 512 bytes smaller
(`absorbX86_64S`): the proof is `absorb`'s over those calls
(`ACall.small`), after the `sub`. -/

open VG.Proof.CmacAes.X86_64 (UpdateSmall ScrSub scrSub_ok scrSub_rel)

/-- `absorbX86_64` with a scratch buffer of 1792 bytes, for `absorbS`. -/
def absorbX86_64S : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 304⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 1792⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 1792 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post := absorbX86_64.post
  pub := absorbX86_64.pub

/-- `APre` after the `sub`, with the 1792 bytes of the scratch buffer as all
of the working space but its first 512 bytes. -/
theorem APre.ofS {s₀ s₁ : State} (h : absorbX86_64S.pre s₀) (a : ScrSub .r9 s₀ s₁) :
    APre s₁ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r9 - BitVec.ofNat 64 512)
      ⟨s₀.gpr .r9 - BitVec.ofNat 64 512 + BitVec.ofNat 64 512, 1792⟩ (s₀.gpr .r8).toNat
      (s₀.gpr .rsi).toNat := by
  obtain ⟨r9₁, g₁, -, rd₁, wr₁⟩ := a
  obtain ⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o, p⟩ := h
  have eS : s₀.gpr .r9 - BitVec.ofNat 64 512 + BitVec.ofNat 64 512 = s₀.gpr .r9 := BitVec.sub_add_cancel _ _
  have sp := g₁ .rsp (by decide)
  rw [eS]
  exact ⟨g₁ _ (by decide), g₁ _ (by decide), by rw [g₁ _ (by decide)], r9₁, by rw [g₁ _ (by decide)],
    by rw [sp]; exact a, by rw [rd₁]; exact b, by rw [wr₁]; exact c, d, e, f, by rw [sp]; exact g,
    by rw [sp]; exact h', by rw [sp]; exact i, by rw [sp]; exact j, by rw [sp]; exact k, by rw [sp]; exact l,
    m, n, o, p, ⟨1664, sub_add_ofNat _ (by decide), by simp⟩⟩

theorem absorbS_wp (v : UpdateImpl) (f : UpdateSmall v.callee) {s₀ : State} (h0 : absorbX86_64S.pre s₀) :
    WP isa (absorbS v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ absorbX86_64S.post s₀ s' := by
  obtain ⟨s₁, run₁, a⟩ := scrSub_ok .r9 s₀
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hp := APre.ofS h0 a
  obtain ⟨-, g₁, m₁, -, -⟩ := a
  refine WP.mono (absorb_wpG (ACall.small v f) hp) fun s' ⟨⟨hs, hr⟩, hpost⟩ => ⟨⟨fun r hr' => ?_, ?_⟩, ?_⟩
  · rw [hs r hr', g₁ r (by rintro rfl; simp [calleeSaved] at hr')]
  · rw [← g₁ .rsp (by decide), hr, m₁]
  · simp only [absorbX86_64S, absorbX86_64] at hpost ⊢
    rw [m₁, g₁ .rdi (by decide), g₁ .rsi (by decide), g₁ .rdx (by decide), g₁ .rcx (by decide),
      g₁ .r8 (by decide)] at hpost
    exact hpost

theorem absorbS_ct (v : UpdateImpl) (f : UpdateSmall v.callee) :
    ConstantTime isa absorbX86_64S.pre absorbX86_64S.pub (absorbS v.callee) := by
  intro s₀ s₀' _ _ _ _ h₁ h₂ hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have r : RelCT isa (fun t₁ t₂ => ∃ a b, (a = s₀ ∧ b = s₀') ∧ ScrSub .r9 a t₁ ∧ ScrSub .r9 b t₂)
      (absorb v.callee) fun _ _ => True := by
    rintro x y t t' x' y' ⟨_, _, ⟨rfl, rfl⟩, a₁, a₂⟩ ex ey
    have hp := APre.ofS h₁ a₁
    have hp' := APre.ofS h₂ a₂
    rw [← q2, ← q5, ← q6, ← q7, ← q3] at hp'
    exact absorb_relG (ACall.small v f) hp hp' (by rw [a₁.2.1 _ (by decide), a₂.2.1 _ (by decide), q1])
      (by rw [a₁.2.1 _ (by decide), a₂.2.1 _ (by decide), q3])
      (by rw [a₁.2.1 _ (by decide), a₂.2.1 _ (by decide), q4]) _ _ _ _ _ _ ⟨rfl, rfl⟩ ex ey
  exact (((scrSub_rel .r9).seq r) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem absorbS_mx (v : UpdateImpl) : (absorbS v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [absorbS, Code.allInstrs, absorb_mx v]; decide +kernel

theorem absorbS_spSafe (v : UpdateImpl) :
    (absorbS v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [absorbS, Code.all, absorb_spSafe v]; decide +kernel

theorem absorbS_correct (v : UpdateImpl) (f : UpdateSmall v.callee) (s : State) (hs : absorbX86_64S.pre s) :
    ∃ t s', Exec isa (absorbS v.callee) s t s' ∧ abiPreserved s s' ∧ absorbX86_64S.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := absorbS_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (absorbS_mx v) he hg, hp⟩

/-- `vg_cmac_aes_absorb` with `scratch: *mut [u64; 224]`, for `absorbS`. -/
def absorbScratchSigS : Sig where
  params := [("state", .array true .u64 38), ("rounds", .int .usize true),
    ("count", .int .u64 true), ("data", .slice false .u8 "len"),
    ("scratch", .array true .u64 224)]

/-- `aesAbsorbContract`, whatever `scratch` is (of 224 words). -/
def absorbScratchContractS {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  absorbScratchSigS.contract A
    (pre := fun state rounds count data len _scratch =>
      Spec.Cmac.aesAbsorbPre A.ptrBits state rounds count data len)
    (post := fun state rounds count data len _scratch =>
      Spec.Cmac.aesAbsorbPost A.ptrBits state rounds count data len)
    (stack := stack)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, with 1792 bytes
of working space. -/
def absorbSatS : State := { absorbSat with wr := [⟨0x1000, 304⟩, ⟨0x4000, 1792⟩] }

theorem absorbS_verified (v : UpdateImpl) (f : UpdateSmall v.callee) :
    Verified X86_64.target (absorbS v.callee) (absorbScratchContractS X86_64.abi 16) :=
  Verified.of_correct (absorbS_correct v f) (absorbS_ct v f) (by
    sig_implies [absorbScratchContractS, absorbScratchSigS, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost,
      absorbX86_64S, absorbX86_64, X86_64.abi, X86_64.argRegs] [absorbSatS, absorbSat] using absorbSatS)

end VG.Proof.CmacAes.Stream.X86_64
