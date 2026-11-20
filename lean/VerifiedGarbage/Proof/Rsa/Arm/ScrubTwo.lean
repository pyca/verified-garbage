module

public import VerifiedGarbage.Impl.Rsa.Arm.WipeTwo
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-!
# Zeroing more stack than one frame holds, with its facts proved (ARMv7)

`Impl.Rsa.Arm.WipeTwo.scrubAll2 rb a b c` is `Impl.Scrub.Arm.scrubAll` for
code whose frames use more than one frame of the model holds: it zeroes the
`a + b` bytes below the stack pointer in two frames, each a frame size of
the model (`FrameOk`). `Verified.scrubAll2` is `Arm.Scrub.Verified.scrubAllS`'s
statement for it, by the same argument: in two runs that agree on what is
public, the wiped bytes are zero before each frame's release, which the two
runs then release from the same stack pointer and the same unknowns
(`pop_mem_congr`), the inner frame first; every other byte is as the code
left it. `verifiedScrubbedAll2` is what a registration binds.
-/

-- separate module: the cleanup of RSASSA-PKCS1-v1_5 signing on ARMv7, apart from the framework it extends.

@[expose] public section

namespace VG.Proof.Rsa.Arm.ScrubTwo

open VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Impl.Scrub.Arm VG.Impl.Rsa.Arm.WipeTwo

/-- What `wipeBelow2 a b` leaks from the stack pointer `sp`: the addresses
of the wiped words of the outer frame, then of the inner. -/
def wipe2Tr (sp : BitVec 32) (a b : Nat) : List Leak :=
  wipeBodyTr (sp - BitVec.ofNat 32 a) a ++ wipeBodyTr (sp - BitVec.ofNat 32 a - BitVec.ofNat 32 b) b

/-- Two releases of a frame from states with the same unknowns leave the
same unknowns. -/
theorem pop_unknowns_congr {j : Instr} {a₁ b₁ c₁ a₂ b₂ c₂ : State} (h₁ : isa.pop j a₁ b₁ = some c₁)
    (h₂ : isa.pop j a₂ b₂ = some c₂) (hu : b₁.unknowns = b₂.unknowns) : c₁.unknowns = c₂.unknowns := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h₁ h₂ <;> split at h₁ <;> split at h₂ <;>
    simp only [Option.some.injEq, reduceCtorEq] at h₁ h₂ <;> subst h₁ h₂ <;> simp only [hu]

theorem allocated_unknowns (n : Nat) (s : State) : (allocated n s).unknowns = s.unknowns := rfl

/-- A run of `wipeBelow2 a b` from `w`: it leaves the registers but `r12`,
`r2` and `r3`, the regions and the stack pointer as they were, changes the
memory only in the `a + b` bytes below the stack pointer, and each of its
frames is released from a state whose stack pointer and unknowns are
functions of `w`'s and in which the frame's bytes are zero (the inner one's,
then all of them). -/
theorem wipeBelow2_run {a b : Nat} (ha : FrameOk a) (hb : FrameOk b) (w : State)
    (hsp : a + b ≤ w.sp.toNat) :
    ∃ u, Exec isa (wipeBelow2 a b) w (wipe2Tr w.sp a b) u ∧
      u.rd = w.rd ∧ u.wr = w.wr ∧ u.sp = w.sp ∧
      (∀ r, r ≠ .r12 → r ≠ .r2 → r ≠ .r3 → u.gpr r = w.gpr r) ∧
      Frame [belowA w.sp (a + b)] w.mem u.mem ∧
      ∃ pa va pb vb, isa.pop (.free a) pa va = some u ∧ va.sp = w.sp - BitVec.ofNat 32 a ∧
        (∀ x, (belowA w.sp a).Contains x 1 → va.mem x = 0) ∧
        isa.pop (.free b) pb vb = some va ∧ vb.sp = w.sp - BitVec.ofNat 32 a - BitVec.ofNat 32 b ∧
        vb.unknowns = w.unknowns ∧
        ∀ x, (belowA (w.sp - BitVec.ofNat 32 a) b).Contains x 1 → vb.mem x = 0 := by
  obtain ⟨h0, h1, h8, henc⟩ := ha
  have hspa : a ≤ w.sp.toNat := by omega
  have hsub : (w.sp - BitVec.ofNat 32 a).toNat = w.sp.toNat - a := sub_toNat' hspa
  have hlt := w.sp.isLt
  let A := allocated a w
  have hR : belowA w.sp a = ⟨State.addr A.sp, a⟩ := by
    simp [A, allocated, belowA, addr_sub' hspa]
  -- The outer frame's bytes zeroed.
  obtain ⟨v, hv, vrd, vwr, vsp, vun, vreg, vf, vz⟩ := wipeBody_run ⟨h0, h1, h8, henc⟩ A (belowA w.sp a)
    (by rw [hR]; simp [A, allocated]) hR (by simp only [A, allocated]; rw [hsub]; omega)
  -- The inner frame's.
  have hvb : b ≤ v.sp.toNat := by rw [vsp]; simp only [A, allocated]; rw [hsub]; omega
  obtain ⟨u₁, vb, hu₁, u₁rd, u₁wr, u₁sp, u₁reg, u₁f, hpopb, vbsp, vbun, vbz⟩ := wipeBelow_run hb v hvb
  have hpush : isa.push (.alloc a) w = some A := by
    simp only [isa, push, h0, h1, h8, henc, hspa, and_self, ite_true]
    rfl
  have hfr : isa.pop (.free a) A u₁ = some { u₁ with
      sp := u₁.sp + BitVec.ofNat 32 a, wr := u₁.wr.tail,
      mem := lose u₁.mem (State.addr u₁.sp) a u₁.unknowns,
      unknowns := fun k => u₁.unknowns (k + a / 2) } := by
    simp only [isa, pop, h0, h1, h8, henc, u₁sp, u₁wr, vsp, vwr, A, allocated, List.head?_cons, and_self, ite_true]
  have hex := Exec.frame hpush (Exec.seq hv hu₁) hfr
  have hvA : v.sp = A.sp := vsp
  refine ⟨_, by simpa [wipe2Tr, addrs, wipeBelow2, A, allocated, hvA] using hex, ?_, ?_, ?_, fun r h12 h2 h3 => ?_,
    ?_, A, u₁, allocated b v, vb, hfr, by rw [u₁sp, vsp]; rfl, fun x hx => ?_,
    hpopb, by rw [vbsp, vsp]; rfl, by rw [vbun, vun]; rfl, fun x hx => vbz x (by rw [vsp]; exact hx)⟩
  · simp [u₁rd, vrd, A, allocated]
  · simp [u₁wr, vwr, A, allocated]
  · simp [u₁sp, vsp, A, allocated, BitVec.sub_add_cancel]
  · simp [u₁reg r h12 h2 h3, vreg r h12 h2 h3, A, allocated]
  · intro x hx
    have hout : ¬ (belowA w.sp (a + b)).Contains x 1 := hx _ (List.mem_singleton_self _)
    have e1 : (⟨State.addr u₁.sp, a⟩ : Region) = belowA w.sp a := by rw [hR, u₁sp, vsp]
    have s1 := belowA_sub (sp := w.sp) (a := a) (b := a + b) (by omega) hsp
    have s2 := belowA_inner (sp := w.sp) (a := b) (b := a + b) (k := a) (by omega) hsp
    show lose u₁.mem (State.addr u₁.sp) a u₁.unknowns x = w.mem x
    rw [lose_frame _ _ _ _ x (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e1]; exact fun h => hout (s1 x h))]
    rw [u₁f x (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [vsp]; exact fun h => hout (s2 x h))]
    exact vf x (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact fun h => hout (s1 x h))
  · rw [hR] at hx
    have hd : (x - State.addr A.sp).toNat < a := by simp only [Region.Contains] at hx; omega
    rw [u₁f x (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      intro hc
      have hB : (State.addr A.sp).toNat = w.sp.toNat - a := by
        simp only [State.addr, BitVec.toNat_setWidth, A, allocated]
        rw [hsub, Nat.mod_eq_of_lt (by omega)]
      have hbl : b < 4096 := hb.2.1
      rw [vsp] at hc
      simp only [Region.Contains] at hc
      rw [addr_sub' (by simp only [A, allocated]; rw [hsub]; omega)] at hc
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at hc hd
      rw [hB] at hc hd
      have hx := x.isLt
      rw [Nat.mod_eq_of_lt (a := b) (by omega)] at hc
      omega)]
    exact vz x hd

/-- A difference of addresses, as a number. -/
theorem toNat_subT (x y : BitVec 64) :
    (x - y).toNat = if y.toNat ≤ x.toNat then x.toNat - y.toNat else 2 ^ 64 - y.toNat + x.toNat := by
  have := x.isLt; have := y.isLt
  rw [BitVec.toNat_sub]; split
  · rw [show 2 ^ 64 - y.toNat + x.toNat = (x.toNat - y.toNat) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)
/-- A byte of the `a + b` bytes below `sp` is among the `a` below `sp` or the
`b` below those. -/
theorem belowA_split {sp : BitVec 32} {a b : Nat} (hsp : a + b ≤ sp.toNat) {x : Addr}
    (hx : (belowA sp (a + b)).Contains x 1) :
    (belowA sp a).Contains x 1 ∨ (belowA (sp - BitVec.ofNat 32 a) b).Contains x 1 := by
  have hl := sp.isLt
  have hS : (State.addr sp).toNat = sp.toNat := by
    simp only [State.addr, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  have hsa : (sp - BitVec.ofNat 32 a).toNat = sp.toNat - a := sub_toNat' (by omega)
  have hS' : (State.addr (sp - BitVec.ofNat 32 a)).toNat = sp.toNat - a := by
    simp only [State.addr, BitVec.toNat_setWidth]; rw [hsa]; exact Nat.mod_eq_of_lt (by omega)
  have base : ∀ (y : Addr) (k : Nat), y.toNat < 2 ^ 32 → k ≤ y.toNat → (y - BitVec.ofNat 64 k).toNat = y.toNat - k :=
    fun y k hy hk => by
      rw [toNat_subT, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp only [hk, ↓reduceIte]
  simp only [Region.Contains] at hx ⊢
  rw [addr_sub' hsp] at hx
  rw [addr_sub' (by omega), addr_sub' (k := b) (by omega)]
  have hxl := x.isLt
  rw [toNat_subT, base _ _ (by omega) (by omega), hS] at hx
  rw [toNat_subT, base _ _ (by omega) (by omega), hS, toNat_subT, base _ _ (by omega) (by omega), hS']
  split at hx <;> split <;> split <;> omega

/-- The registers `tail` sets, but the result. -/
theorem tail_zeroed2 (r : Reg) (h0 : r ≠ .r0) (h1 : r ≠ .r1) (hr : r ∉ preserved) :
    r = .r2 ∨ r = .r3 ∨ r = .r12 := by
  revert h0 h1 hr; cases r <;> decide

/-- A run of `scrubAll2 rb a b c` from `s`, after `c`'s run to `w`: as
`Arm.Scrub.scrubAll_run`, with each frame of the wipe released from a state in
which its bytes are zero. -/
theorem scrubAll2_run {rb a b : Nat} (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) (ha : FrameOk a) (hb : FrameOk b)
    {c : Prog isa} (hd : armStack c ≤ a + b) {s w : State} {t : List Leak} (hsp : a + b ≤ s.sp.toNat)
    (he : Exec isa c s t w) :
    ∃ u, Exec isa (scrubAll2 rb a b c) s (t ++ (wipe2Tr s.sp a b ++ [])) u ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ (∀ r ∈ preserved, u.gpr r = w.gpr r) ∧
      u.gpr .r2 = 0 ∧ u.gpr .r3 = 0 ∧ u.gpr .r12 = 0 ∧
      u.n = false ∧ u.z = true ∧ u.c = true ∧ u.v = false ∧
      (u.gpr .r1 ++ u.gpr .r0) >>> rb = 0 ∧
      (u.gpr .r1 ++ u.gpr .r0).setWidth rb = (w.gpr .r1 ++ w.gpr .r0).setWidth rb ∧
      (∃ u' pa va pb vb, isa.pop (.free a) pa va = some u' ∧ u.mem = u'.mem ∧
        va.sp = s.sp - BitVec.ofNat 32 a ∧ (∀ x, (belowA s.sp a).Contains x 1 → va.mem x = 0) ∧
        isa.pop (.free b) pb vb = some va ∧ vb.sp = s.sp - BitVec.ofNat 32 a - BitVec.ofNat 32 b ∧
        vb.unknowns = w.unknowns ∧
        ∀ x, (belowA (s.sp - BitVec.ofNat 32 a) b).Contains x 1 → vb.mem x = 0) ∧
      (∀ x, ¬ (belowA s.sp (a + b)).Contains x 1 → u.mem x = w.mem x) ∧
      Frame (s.wr ++ [belowA s.sp (a + b)]) s.mem w.mem := by
  obtain ⟨hrd, hwr, hp⟩ := Exec.rdwr he
  have hfs := Frame.belowA_mono (Exec.frameSp he (Nat.le_trans hd hsp)) hd hsp
  obtain ⟨v, hv, vrd, vwr, vsp, vreg, vf, pa, va, pb, vb, hpa, vasp, vaz, hpb, vbsp, vbun, vbz⟩ :=
    wipeBelow2_run ha hb w (hp ▸ hsp)
  obtain ⟨u, hbk, hm, urd, uwr, usp, upres, h2, h3, h12, fn, fz, fc, fv, hsh, hret⟩ := tail_run hrb v
  rw [hp] at hv vf vasp vaz vbsp vbz
  refine ⟨u, .seq he (.seq hv (.block hbk)), urd.trans (vrd.trans hrd), uwr.trans (vwr.trans hwr),
    usp.trans (vsp.trans hp), fun r hr => ?_, h2, h3, h12, fn, fz, fc, fv, hsh, ?_,
    ⟨v, pa, va, pb, vb, hpa, hm, vasp, vaz, hpb, vbsp, vbun, vbz⟩, fun x hx => ?_, hfs⟩
  · rw [upres r hr]
    exact vreg r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
      (by rintro rfl; simp [preserved] at hr)
  · rw [hret, vreg .r1 (by decide) (by decide) (by decide), vreg .r0 (by decide) (by decide) (by decide)]
  · rw [hm]; exact vf x fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hx

/-- `scrubAll2 rb a b c` meets the contract of `c`, whose frames use at most
the `a + b` bytes the contract reserves and which makes no indirect call, and
whose postcondition reads the memory on return only within the buffers, and
returns without secret residue: `Arm.Scrub.Verified.scrubAllS`, with the stack
wiped in two frames. -/
theorem Verified.scrubAll2 {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {a b : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa}
    (hv : Verified target c (sig.contract A pre post wa (a + b) leak)) (hd : armStack c ≤ a + b)
    (hni : noIcall c = true) (ha : FrameOk a) (hb : FrameOk b) {rb : Nat} (e : rb = sig.retBits A.ptrBits)
    (hpost : PostOut (sig.contract A pre post wa (a + b) leak) rb) :
    Verified target (Impl.Rsa.Arm.WipeTwo.scrubAll2 rb a b c) (sig.contract A pre post wa (a + b) leak) ∧
      NoResidue (Impl.Rsa.Arm.WipeTwo.scrubAll2 rb a b c) (sig.contract A pre post wa (a + b) leak) rb := by
  have hrb : rb = 0 ∨ rb = 32 ∨ rb = 64 := by rw [e, hA.ptrBits]; exact retBits_cases sig
  have h0 : a + b ≠ 0 := by have := ha.1; omega
  have hsy : ∀ s₁ s₂, (sig.contract A pre post wa (a + b) leak).pub s₁ s₂ →
      ∀ n ∈ inames c, isa.fnAddr s₁ n = isa.fnAddr s₂ n :=
    fun _ _ _ n hn => absurd hn (by rw [inames_of_noIcall hni]; exact List.not_mem_nil)
  -- Every run is `c`'s run, then the wipe and the tail.
  have run : ∀ {s u : State} {T : List Leak}, (sig.contract A pre post wa (a + b) leak).pre s →
      Exec isa (Impl.Rsa.Arm.WipeTwo.scrubAll2 rb a b c) s T u → ∃ t w, Exec isa c s t w ∧
        T = t ++ (wipe2Tr s.sp a b ++ []) ∧
        u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ (∀ r ∈ preserved, u.gpr r = w.gpr r) ∧
        u.gpr .r2 = 0 ∧ u.gpr .r3 = 0 ∧ u.gpr .r12 = 0 ∧
        u.n = false ∧ u.z = true ∧ u.c = true ∧ u.v = false ∧
        (u.gpr .r1 ++ u.gpr .r0) >>> rb = 0 ∧
        (u.gpr .r1 ++ u.gpr .r0).setWidth rb = (w.gpr .r1 ++ w.gpr .r0).setWidth rb ∧
        (∃ u' pa va pb vb, isa.pop (.free a) pa va = some u' ∧ u.mem = u'.mem ∧
          va.sp = s.sp - BitVec.ofNat 32 a ∧ (∀ x, (belowA s.sp a).Contains x 1 → va.mem x = 0) ∧
          isa.pop (.free b) pb vb = some va ∧ vb.sp = s.sp - BitVec.ofNat 32 a - BitVec.ofNat 32 b ∧
          vb.unknowns = w.unknowns ∧
          ∀ x, (belowA (s.sp - BitVec.ofNat 32 a) b).Contains x 1 → vb.mem x = 0) ∧
        (∀ x, ¬ (belowA s.sp (a + b)).Contains x 1 → u.mem x = w.mem x) ∧
        Frame (s.wr ++ [belowA s.sp (a + b)]) s.mem w.mem := by
    intro s u T hs h
    cases h with
    | seq x y =>
      rename_i w t₁ t₂
      obtain ⟨u', hu', facts⟩ := scrubAll2_run hrb ha hb hd (contract_pre_scrub hA hs h0).1 x
      obtain ⟨hT, rfl⟩ := Exec.det (Exec.seq x y) hu'
      exact ⟨t₁, w, x, hT, facts⟩
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ hp e₁ e₂ => ?_, hv.2.2⟩, ?_⟩
  · obtain ⟨t, w, he, habi, hq⟩ := hv.1 s hs
    obtain ⟨hsp, hdis⟩ := contract_pre_scrub hA hs h0
    obtain ⟨u, hu, -, -, usp, upres, -, -, -, -, -, -, -, -, hret, -, hkeep, -⟩ :=
      scrubAll2_run hrb ha hb hd hsp he
    refine ⟨_, u, hu, ⟨fun r hr => (upres r hr).trans (habi.1 r hr), usp⟩,
      hpost s w u hs hq (fun x ⟨r, hr, hx⟩ => hkeep x fun hb => hdis r hr x hb hx) hret⟩
  · obtain ⟨a₁, w₁, x₁, rfl, -⟩ := run p₁ e₁
    obtain ⟨a₂, w₂, x₂, rfl, -⟩ := run p₂ e₂
    rw [hv.2.1 s₁ s₂ a₁ a₂ w₁ w₂ p₁ p₂ hp x₁ x₂, contract_pub_sp hA hp]
  · intro s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ hp ho hu e₁ e₂
    obtain ⟨a₁, w₁, x₁, -, rd₁, wr₁, sp₁, pr₁, x2, x3, x12, n₁, z₁, c₁, v₁, r₁, -, zero₁, keep₁, f₁⟩ := run p₁ e₁
    obtain ⟨a₂, w₂, x₂, -, rd₂, wr₂, sp₂, pr₂, y2, y3, y12, n₂, z₂, c₂, v₂, r₂, -, zero₂, keep₂, f₂⟩ := run p₂ e₂
    obtain ⟨ord, owr, oreg, -, osp, -, -, -, -, omem⟩ := ho
    -- The two runs of `c` leak the same trace, so end with the same unknowns.
    have hw : w₁.unknowns = w₂.unknowns :=
      (Exec.pathS x₁ (r₁ := []) (r₂ := []) x₂ (hsy s₁ s₂ hp)
        (by rw [hv.2.1 s₁ s₂ a₁ a₂ w₁ w₂ p₁ p₂ hp x₁ x₂]) hu).2
    -- Each run keeps what the calling convention preserves.
    have abi₁ : ∀ r ∈ preserved, w₁.gpr r = s₁.gpr r := by
      obtain ⟨t', w', a', habi, -⟩ := hv.1 s₁ p₁
      obtain ⟨-, rfl⟩ := Exec.det x₁ a'
      exact habi.1
    have abi₂ : ∀ r ∈ preserved, w₂.gpr r = s₂.gpr r := by
      obtain ⟨t', w', a', habi, -⟩ := hv.1 s₂ p₂
      obtain ⟨-, rfl⟩ := Exec.det x₂ a'
      exact habi.1
    have hsp₁ : a + b ≤ s₁.sp.toNat := (contract_pre_scrub hA p₁ h0).1
    refine ⟨rd₁.trans (ord.trans rd₂.symm), wr₁.trans (owr.trans wr₂.symm), fun r h0 h1 => ?_,
      r₁.trans r₂.symm, sp₁.trans (osp.trans sp₂.symm), n₁.trans n₂.symm, z₁.trans z₂.symm,
      c₁.trans c₂.symm, v₁.trans v₂.symm, fun x hx => ?_⟩
    · by_cases hr : r ∈ preserved
      · rw [pr₁ r hr, pr₂ r hr, abi₁ r hr, abi₂ r hr]; exact oreg r h0 h1
      · obtain rfl | rfl | rfl := tail_zeroed2 r h0 h1 hr
        · exact x2.trans y2.symm
        · exact x3.trans y3.symm
        · exact x12.trans y12.symm
    · rw [rd₁, wr₁] at hx
      by_cases hb' : (belowA s₁.sp (a + b)).Contains x 1
      · obtain ⟨u₁', pa₁, va₁, pb₁, vb₁, hpa₁, hm₁, vasp₁, vaz₁, hpb₁, vbsp₁, vbun₁, vbz₁⟩ := zero₁
        obtain ⟨u₂', pa₂, va₂, pb₂, vb₂, hpa₂, hm₂, vasp₂, vaz₂, hpb₂, vbsp₂, vbun₂, vbz₂⟩ := zero₂
        have hvb : vb₁.unknowns = vb₂.unknowns := by rw [vbun₁, vbun₂, hw]
        -- Before the outer frame's release, the two runs' bytes are the same: zero in the
        -- outer frame, and in the inner one what its release from zeros left.
        have hva : va₁.mem x = va₂.mem x := by
          rcases belowA_split hsp₁ hb' with ho' | hi'
          · exact (vaz₁ x ho').trans (vaz₂ x (osp ▸ ho')).symm
          · exact pop_mem_congr hpb₁ hpb₂ (by rw [vbsp₁, vbsp₂, osp]) hvb
              ((vbz₁ x hi').trans (vbz₂ x (osp ▸ hi')).symm)
        rw [hm₁, hm₂]
        exact pop_mem_congr hpa₁ hpa₂ (by rw [vasp₁, vasp₂, osp]) (pop_unknowns_congr hpb₁ hpb₂ hvb) hva
      · rw [keep₁ x hb', keep₂ x (osp ▸ hb'),
          f₁ x fun r hr => by
            rcases List.mem_append.mp hr with hr | hr
            · exact hx r (List.mem_append_right _ hr)
            · simp only [List.mem_singleton] at hr; subst hr; exact hb',
          f₂ x fun r hr => by
            rcases List.mem_append.mp hr with hr | hr
            · exact hx r (List.mem_append_right _ (owr ▸ hr))
            · simp only [List.mem_singleton] at hr; subst hr; exact osp ▸ hb']
        exact omem x hx

/-- `r`'s code, whose frames use at most the `a + b` bytes of stack its
contract reserves and which makes no indirect call, with its cleanup
(`scrubAll2`: those bytes zeroed in two frames, the result's `rb` bits kept)
meets `r`'s contract in constant time and returns without secret residue, if
its postcondition reads the memory on return only within the buffers
(`PostOut`): `Arm.Scrub.verifiedScrubbedAll`, for a stack of more than one
frame, as the theorem about the code that a registration binds. -/
theorem verifiedScrubbedAll2 {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {a b : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa}
    (hv : Verified target c (sig.contract abi pre post wa (a + b) leak)) (hok : CodeOk c (a + b))
    (ha : FrameOk a) (hb : FrameOk b) {rb : Nat} (e : rb = sig.retBits abi.ptrBits)
    (hpost : PostOut (sig.contract abi pre post wa (a + b) leak) rb) :
    VerifiedScrubbed target (scrubAll2 rb a b c) (sig.contract abi pre post wa (a + b) leak) rb :=
  have h := Verified.scrubAll2 ScrubAbi.plain hv hok.1 hok.2 ha hb e hpost
  ⟨h.1, h.2⟩

end VG.Proof.Rsa.Arm.ScrubTwo
