module

-- separate module: a call of any `thash4`, for `forsPk`'s proofs as well as `xmssPk`'s

public import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4Impl
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA on x86-64: a call of `thash4`

`thash4_call`: a call of any implementation of `thash4` (`Thash4Impl`) from
a state whose arguments meet its contract, its four lanes `⟨L, 4·str⟩` and
its `work` writable: the caller's state after it has the outputs, `SHAKE256`
of the messages as they were before the call, and changes only them, `work`
but its table of round constants, and the stack its calls take below the
caller's stack pointer (8 bytes more than the implementation's own, for
the return address).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Spec.Sha3 (bytesAt shake256)

/-- The regions a call of `thash4` on the lanes `⟨L, 4·str⟩` and `work` at
`W`, from the stack pointer `sp`, may change. -/
def t4Changes (n stack : Nat) (L W sp : Addr) (str : Nat) : List Region :=
  ((List.range 4).map fun k => ⟨L + BitVec.ofNat 64 (n + 32) + BitVec.ofNat 64 (k * str), n⟩) ++
    [⟨W, 1600⟩, ⟨W + BitVec.ofNat 64 2368, workLen - 2368⟩, below sp (stack + 8)]

theorem bytesAt_congr {m m' : Mem} {p : Addr} {c : Nat} (h : ∀ i < c, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    bytesAt m' p c = bytesAt m p c :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- The precondition of `thash4` on entry to a call of it. -/
theorem thash4_entry {n : Nat} (T : Thash4Impl n) {s : State} {L W : Addr} {str len : Nat}
    (hdi : s.gpr .rdi = L) (hsi : (s.gpr .rsi).toNat = str) (hdx : (s.gpr .rdx).toNat = len)
    (hcx : s.gpr .rcx = L + BitVec.ofNat 64 (n + 32)) (h8 : s.gpr .r8 = W)
    (hpos : 0 < len) (hmod : len % 8 = 0) (hle : len ≤ str) (hout : n + 32 + n ≤ str)
    (hfitL : L.toNat + 4 * str ≤ 2 ^ 64) (hfitW : W.toNat + workLen ≤ 2 ^ 64)
    (hLW : Region.Disjoint ⟨L, 4 * str⟩ ⟨W, workLen⟩)
    (hsL : (below (s.gpr .rsp) (T.stack + 8)).Disjoint ⟨L, 4 * str⟩)
    (hsW : (below (s.gpr .rsp) (T.stack + 8)).Disjoint ⟨W, workLen⟩)
    (hrc : RcTable s.mem W) :
    Thash4Pre n T.stack (s.callEntry.withRegions [] [⟨L, 4 * str⟩, ⟨W, workLen⟩]) := by
  have hst := T.stack_le
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  -- the return address, in the stack the call takes
  have hret : Region.Sub ⟨s.gpr .rsp - 8, 8⟩ (below (s.gpr .rsp) (T.stack + 8)) :=
    Offset.sub_below (s.gpr .rsp) (a := 8) (b := T.stack + 8) (by omega) (by omega)
  have hstk : Region.Sub (below (s.gpr .rsp - 8) T.stack) (below (s.gpr .rsp) (T.stack + 8)) :=
    below_callee _ _
  have hb8 : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) (T.stack + 8)) :=
    below_sub (by omega) (by omega)
  -- the call stores its return address and nothing else
  have hfE : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
    rw [State.callEntry_mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega))
  have hdE : ∀ {R : Region}, Region.Sub R (below (s.gpr .rsp) (T.stack + 8)) ∨
      (below (s.gpr .rsp) (T.stack + 8)).Disjoint R → (below (s.gpr .rsp) (T.stack + 8)).Disjoint R →
      ∀ r ∈ [below (s.gpr .rsp) 8], R.Disjoint r := fun _ hd r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact (hd.sub_left hb8).symm
  show Thash4Pre n T.stack _
  have g : ∀ r : Reg, r ≠ .rsp → (s.callEntry.withRegions [] [⟨L, 4 * str⟩, ⟨W, workLen⟩]).gpr r = s.gpr r :=
    fun r h => by rw [State.withRegions_gpr, hne r h]
  have gsp : (s.callEntry.withRegions [] [⟨L, 4 * str⟩, ⟨W, workLen⟩]).gpr .rsp = s.gpr .rsp - 8 := by
    rw [State.withRegions_gpr, State.callEntry_rsp]
  have gm : (s.callEntry.withRegions [] [⟨L, 4 * str⟩, ⟨W, workLen⟩]).mem = s.callEntry.mem := State.withRegions_mem _ _ _
  have rdi' := g .rdi (by decide); have rsi' := g .rsi (by decide); have rdx' := g .rdx (by decide)
  have rcx' := g .rcx (by decide); have r8' := g .r8 (by decide)
  rw [hdi] at rdi'; rw [h8] at r8'; rw [hcx] at rcx'
  have hdisR : ∀ r < 24, ∀ k < 4, Region.Sub ⟨W + BitVec.ofNat 64 (1600 + 32 * r + 8 * k), 8⟩ ⟨W, workLen⟩ :=
    fun r hr k hk => Offset.sub_base W (by simp only [workLen]; omega_using [hr, hk])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact State.withRegions_rd _ _ _
  · rw [State.withRegions_wr, rdi', rsi', r8', hsi]
  · rw [rdi', rsi', r8', hsi]; exact hLW
  · rw [rdi', rsi', retR, gsp, hsi]; exact hsL.sub_left hret
  · rw [r8', retR, gsp]; exact hsW.sub_left hret
  · rw [rdi', rsi', gsp, hsi]; exact hsL.sub_left hstk
  · rw [r8', gsp]; exact hsW.sub_left hstk
  · rw [rdi', rsi', hsi]; exact hfitL
  · rw [r8']; exact hfitW
  · rw [rdx', hdx]; exact hpos
  · rw [rdx', hdx]; exact hmod
  · rw [rdx', rsi', hdx, hsi]; exact hle
  · rw [rcx', rdi']
  · rw [rsi', hsi]; exact hout
  · rw [gm, r8']
    intro r hr k hk
    rw [← hrc r hr k hk]
    exact hfE.readW (r := ⟨W + BitVec.ofNat 64 (1600 + 32 * r + 8 * k), 8⟩)
      (by simp [Region.Contains]) (hdE (.inr (hsW.sub_right (hdisR r hr k hk))) (hsW.sub_right (hdisR r hr k hk)))
      (by decide)

/-- A call of `thash4`. -/
theorem thash4_call {n : Nat} (T : Thash4Impl n) (name : String) {s : State} {L W : Addr} {str len : Nat}
    (hdi : s.gpr .rdi = L) (hsi : (s.gpr .rsi).toNat = str) (hdx : (s.gpr .rdx).toNat = len)
    (hcx : s.gpr .rcx = L + BitVec.ofNat 64 (n + 32)) (h8 : s.gpr .r8 = W)
    (hpos : 0 < len) (hmod : len % 8 = 0) (hle : len ≤ str) (hout : n + 32 + n ≤ str)
    (hfitL : L.toNat + 4 * str ≤ 2 ^ 64) (hfitW : W.toNat + workLen ≤ 2 ^ 64)
    (hLW : Region.Disjoint ⟨L, 4 * str⟩ ⟨W, workLen⟩)
    (hsL : (below (s.gpr .rsp) (T.stack + 8)).Disjoint ⟨L, 4 * str⟩)
    (hsW : (below (s.gpr .rsp) (T.stack + 8)).Disjoint ⟨W, workLen⟩)
    (hrc : RcTable s.mem W) (hcov : Covers [⟨L, 4 * str⟩, ⟨W, workLen⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      (∀ k < 4, bytesAt s'.mem (L + BitVec.ofNat 64 (n + 32) + BitVec.ofNat 64 (k * str)) n =
        shake256 (bytesAt s.mem (L + BitVec.ofNat 64 (k * str)) len) n) →
      Frame (t4Changes n T.stack L W (s.gpr .rsp) str) s.mem s'.mem → Q s') :
    WP isa (.call name T.code) s Q := by
  have hst := T.stack_le
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  -- the return address, in the stack the call takes
  have hret : Region.Sub ⟨s.gpr .rsp - 8, 8⟩ (below (s.gpr .rsp) (T.stack + 8)) :=
    Offset.sub_below (s.gpr .rsp) (a := 8) (b := T.stack + 8) (by omega) (by omega)
  have hstk : Region.Sub (below (s.gpr .rsp - 8) T.stack) (below (s.gpr .rsp) (T.stack + 8)) :=
    below_callee _ _
  have hb8 : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) (T.stack + 8)) :=
    below_sub (by omega) (by omega)
  -- the call stores its return address and nothing else
  have hfE : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
    rw [State.callEntry_mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega))
  have hdE : ∀ {R : Region}, Region.Sub R (below (s.gpr .rsp) (T.stack + 8)) ∨
      (below (s.gpr .rsp) (T.stack + 8)).Disjoint R → (below (s.gpr .rsp) (T.stack + 8)).Disjoint R →
      ∀ r ∈ [below (s.gpr .rsp) 8], R.Disjoint r := fun _ hd r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact (hd.sub_left hb8).symm
  refine WP.call (k := thash4Contract n T.stack) T.verified.1 T.nosp (by have := T.depth_le; omega)
    (rd := []) (wr := [⟨L, 4 * str⟩, ⟨W, workLen⟩]) ?_ ?_ hcov ?_
  · exact thash4_entry T hdi hsi hdx hcx h8 hpos hmod hle hout hfitL hfitW hLW hsL hsW hrc
  · intro a m h
    obtain ⟨r, hr, hc⟩ := hcov a m (by simpa using h)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro s' hrd hwr hcs _ _ ⟨s₂, hm₂, _, hpost, hfr⟩
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp,
      hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp),
      hne _ (by decide : Reg.rcx ≠ .rsp), hne _ (by decide : Reg.r8 ≠ .rsp), outAt, msg, hdi, hsi, hdx, hcx, h8,
      thash4Changes, hm₂] at hpost hfr
    refine hQ s' hrd hwr hcs (fun k hk => ?_) ?_
    · rw [hpost k hk]
      refine congrArg (shake256 · n) (bytesAt_congr fun i hi => ?_)
      have hlane : Region.Sub ⟨L + BitVec.ofNat 64 (k * str), len⟩ ⟨L, 4 * str⟩ :=
        Offset.sub_base L (by
          have : k * str + str ≤ 4 * str := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
          omega)
      exact hfE.bytes (R := ⟨L + BitVec.ofNat 64 (k * str), len⟩) (hdE (.inr (hsL.sub_right hlane))
        (hsL.sub_right hlane)) (by show len ≤ 2 ^ 64; omega) hi
    · let U : List Region :=
        ((List.range 4).map fun k => (⟨L + BitVec.ofNat 64 (n + 32) + BitVec.ofNat 64 (k * str), n⟩ : Region)) ++
          [⟨W, 1600⟩, ⟨W + BitVec.ofNat 64 2368, workLen - 2368⟩, below (s.gpr .rsp - 8) T.stack,
            below (s.gpr .rsp) 8]
      have h1 : Frame U s.mem s.callEntry.mem := Frame.mono hfE fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; simp [U]
      have h2 : Frame U s.callEntry.mem s'.mem := Frame.mono hfr fun r hr => by
        simp only [U, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
          or_false] at hr ⊢
        rcases hr with hr | hr | hr | hr
        · exact .inl hr
        · exact .inr (.inl hr)
        · exact .inr (.inr (.inl hr))
        · exact .inr (.inr (.inr (.inl hr)))
      refine (h1.trans h2).sub fun r hr => ?_
      simp only [U, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
        or_false] at hr
      simp only [t4Changes, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
        or_false]
      rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl | rfl
      · exact ⟨_, .inl ⟨k, hk, rfl⟩, fun _ h => h⟩
      · exact ⟨_, .inr (.inl rfl), fun _ h => h⟩
      · exact ⟨_, .inr (.inr (.inl rfl)), fun _ h => h⟩
      · exact ⟨_, .inr (.inr (.inr rfl)), hstk⟩
      · exact ⟨_, .inr (.inr (.inr rfl)), hb8⟩

end VG.Proof.SlhDsa.X86_64
