module

public import VerifiedGarbage.Proof.Hmac.Any.X86_64.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Tier
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkCalls
public import VerifiedGarbage.Proof.Framework.X86_64.Dispatch
public import VerifiedGarbage.Impl.Hmac.Any.X86_64
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-!
# HMAC and streaming `update` with the hash function as an argument on x86-64: the proofs

For hash functions `vs` (an `MdHash` for each number of `hashIds`, whose
`Instance` is the one `inst` gives it: `Good`), each function moves `hash`
into `rax` (`ldSel_wp`) and the dispatch on it (`chain_wp`) calls that hash
function's: HMAC's `init` (`hinit_call`) or `finalize` (`hfin_call`), or the
streaming `update` (`upd_call`), with the arguments where it takes them,
within the buffers of the hash function, which lie at the start of ours
(`init_args`, …). Their contracts give ours (`init_wp`, …). Two runs with
the same `hash` dispatch alike and call the same function, constant time
(`init_ct`, …).
-/

@[expose] public section

namespace VG.Proof.Hmac.Any.X86_64

open VG.X86_64
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Hmac.Any (inst hashIds)
open Spec.Sha256 (bytesAt)
open VG.Impl.Hmac.Any.X86_64 (ldSel)
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash HashOK Tier core_updC hmacInit_ok hmacFin_ok core_hmacInit core_hmacFin
  core_hmacInit_depth core_hmacFin_depth nosp_of)
open VG.Proof.Pbkdf2.Md.X86_64.Pbk (InitArgs FinArgs hinit_call hinit_rel hfin_call hfin_rel)
open VG.Proof.Dispatch.X86_64 (FlagsOnly)
open VG.Proof.Pbkdf2.Md.X86_64 (Calls.UpdArgs Calls.upd_call Calls.upd_rel)

/-! ## The hash functions -/

/-- An implementation of each hash function `hashIds` numbers, of the
`Instance` `inst` gives it. -/
structure Good (vs : List (Nat × MdHash)) : Prop where
  keys : vs.map (·.1) = hashIds
  inst : ∀ k v, (k, v) ∈ vs → inst k = some v.I

/-- The hash functions' code, by number. -/
def hsOf (vs : List (Nat × MdHash)) : List (Nat × Impl.Pbkdf2.Md.X86_64.Hash) :=
  vs.map fun p => (p.1, p.2.H)

/-- The sizes of the instances `inst` gives: within our buffers. -/
theorem inst_sizes {k : Nat} (hk : k ∈ hashIds) {I : Spec.Hmac.Instance} (hI : inst k = some I) :
    I.S.stateBytes ≤ 192 ∧ I.scratch ≤ 234 ∧ I.S.digestBytes ≤ 64 := by
  simp only [hashIds, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [inst, Option.some.injEq] at hI <;> subst hI <;> decide

/-- The sizes of `v`, the hash function `k` names. -/
theorem sizes {vs : List (Nat × MdHash)} (G : Good vs) {k : Nat} {v : MdHash} (hm : (k, v) ∈ vs) :
    v.H.S = v.I.S.stateBytes ∧ v.H.S ≤ 192 ∧ v.H.W ≤ 234 ∧ v.H.D ≤ 64 ∧
      v.H.P.B = v.I.S.H.blockSize ∧ v.H.D = v.I.S.digestBytes := by
  have hk : k ∈ hashIds := by rw [← G.keys]; exact List.mem_map.mpr ⟨_, hm, rfl⟩
  obtain ⟨h1, h2, h3⟩ := inst_sizes hk (G.inst k v hm)
  have hS := v.ok.hS; have hB := v.ok.hB; have hD := v.ok.hD
  rw [v.hSH] at hS hB hD
  have hW := v.hW
  refine ⟨hS.symm, ?_, ?_, ?_, hB.symm, hD.symm⟩
  · show v.H.P.N + v.H.P.B ≤ 192; omega
  · omega
  · omega

/-- The cases of a dispatch over `vs`, by their numbers. -/
theorem keys_map {vs : List (Nat × MdHash)} (G : Good vs)
    (g : Nat × Impl.Pbkdf2.Md.X86_64.Hash → Nat × Prog isa) (hg : ∀ p, (g p).1 = p.1) :
    Proof.Dispatch.keys ((hsOf vs).map g) = hashIds := by
  simp only [Proof.Dispatch.keys, hsOf, List.map_map]
  rw [← G.keys]
  exact List.map_congr_left fun p _ => hg _

theorem mem_map {vs : List (Nat × MdHash)} {g : Nat × Impl.Pbkdf2.Md.X86_64.Hash → Nat × Prog isa}
    (hg : ∀ p, (g p).1 = p.1) {k : Nat} {c : Prog isa} (h : (k, c) ∈ (hsOf vs).map g) :
    ∃ v, (k, v) ∈ vs ∧ g (k, v.H) = (k, c) := by
  simp only [hsOf, List.map_map, List.mem_map, Function.comp] at h
  obtain ⟨⟨k', v⟩, hm, e⟩ := h
  have hk : k' = k := by have := congrArg Prod.fst e; rw [hg] at this; exact this
  subst hk
  exact ⟨v, hm, e⟩

theorem keys_lt : ∀ k ∈ hashIds, k < 2 ^ 31 := by decide

theorem keys_nodup : hashIds.Nodup := by decide

/-! ## Moving `hash` into `rax` -/

theorem ldSel_exec (s : State) : Exec isa (.block ldSel) s [] (s.setReg .rax (s.gpr .r9)) :=
  Exec.block rfl

theorem ldSel_wp (s : State) : WP isa (.block ldSel) s fun s₁ => s₁ = s.setReg .rax (s.gpr .r9) :=
  ⟨[], _, ldSel_exec s, rfl⟩

theorem ldSel_mx : (Code.block ldSel : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by decide

theorem test_mx (k : Nat) :
    (Code.block (Impl.Dispatch.X86_64.test k) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := rfl

/-- The selector after `ldSel`. -/
theorem sel_ld (s : State) : Proof.Dispatch.X86_64.sel (s.setReg .rax (s.gpr .r9)) = (s.gpr .r9).toNat := by
  simp [Proof.Dispatch.X86_64.sel, State.setReg]

theorem rax_notCs {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rax := by
  rintro rfl; exact absurd hr (by decide)

/-- The state a case starts in: `rax` is `hash`, the flags may differ, and
the rest is as on entry. -/
structure AtCase (s u : State) : Prop where
  gpr : ∀ r, r ≠ .rax → u.gpr r = s.gpr r
  rax : u.gpr .rax = s.gpr .r9
  mem : u.mem = s.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr

theorem AtCase.of {s s₁ u : State} (h₁ : s₁ = s.setReg .rax (s.gpr .r9)) (hf : FlagsOnly s₁ u) : AtCase s u where
  gpr r hr := by rw [hf.gpr, h₁]; simp [State.setReg, hr]
  rax := by rw [hf.gpr, h₁]; simp [State.setReg]
  mem := by rw [hf.mem, h₁]; rfl
  rd := by rw [hf.rd, h₁]; rfl
  wr := by rw [hf.wr, h₁]; rfl

theorem AtCase.rsp {s u : State} (h : AtCase s u) : u.gpr .rsp = s.gpr .rsp := h.gpr _ (by decide)

/-- The selector of a case is `hash`. -/
theorem AtCase.sel {s u : State} (h : AtCase s u) : Dispatch.X86_64.sel u = (s.gpr .r9).toNat := by
  simp only [Dispatch.X86_64.sel, h.rax]

/-! ## Our buffers and theirs -/

/-- The first `n` bytes of a region. -/
theorem psub (p : Addr) {n k : Nat} (h : n ≤ k) : Region.Sub ⟨p, n⟩ ⟨p, k⟩ := by
  have := Offset.sub_base p (d := 0) (n := n) (k := k) (by omega)
  simpa using this

theorem covers_pre {p : Addr} {n k : Nat} (h : n ≤ k) {rs : List Region} (hm : (⟨p, k⟩ : Region) ∈ rs) :
    ∃ r' ∈ rs, ∃ off, (⟨p, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧ off + (⟨p, n⟩ : Region).len ≤ r'.len :=
  ⟨_, hm, 0, by simp, by simpa using h⟩

/-- After a call, the return address: neither a region it may write nor the
`n` bytes of stack below `rsp` it uses overlaps it. -/
theorem ret_kept {s s' : State} {ws : List Region} {n : Nat} (hn : n < 2 ^ 63)
    (hf : Frame (ws ++ [below (s.gpr .rsp) n]) s.mem s'.mem)
    (hd : ∀ r ∈ ws, (⟨s.gpr .rsp, 8⟩ : Region).Disjoint r) :
    s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · exact hd r hr
  · simp only [List.mem_singleton] at hr; subst hr
    have := Offset.disjoint_below (s.gpr .rsp) (n := n) (d := 0) (k := 8) (by omega)
    simpa using this

/-- Two runs after `ldSel`, from states satisfying `P`. -/
def AfterLd (P : State → State → Prop) (s₁ s₂ : State) : Prop :=
  ∃ a₁ a₂, P a₁ a₂ ∧ s₁ = a₁.setReg .rax (a₁.gpr .r9) ∧ s₂ = a₂.setReg .rax (a₂.gpr .r9)

theorem ldSel_rel (P : State → State → Prop) : RelCT isa P (.block ldSel) (AfterLd P) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rfl, rfl⟩ := Exec.det e₁ (ldSel_exec s₁)
  obtain ⟨rfl, rfl⟩ := Exec.det e₂ (ldSel_exec s₂)
  exact ⟨rfl, s₁, s₂, hp, rfl, rfl⟩

/-! ## `init` -/

section Init

variable {vs : List (Nat × MdHash)} (G : Good vs)
include G

theorem init_args {s u : State} (hs : initA.pre s) (hu : AtCase s u) {k : Nat} {v : MdHash} (hm : (k, v) ∈ vs)
    (hk : (s.gpr .r9).toNat = k) :
    InitArgs (H := v.H) u (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .rcx).toNat := by
  obtain ⟨⟨_, hkl⟩, hrd, hwr, i_o, i_s, o_s, k_i, k_o, k_s, -, -, -, t_i, t_o, t_k, t_s, hsc⟩ := hs
  obtain ⟨hS, hS192, hW, -, hB, -⟩ := sizes G hm
  have hkl' := hkl v.I (by rw [hk]; exact G.inst k v hm)
  have si : Region.Sub ⟨s.gpr .rdi, v.H.S⟩ ⟨s.gpr .rdi, 192⟩ := psub _ hS192
  have so : Region.Sub ⟨s.gpr .rsi, v.H.S⟩ ⟨s.gpr .rsi, 192⟩ := psub _ hS192
  have ss : Region.Sub ⟨s.gpr .r8, 8 * v.H.W⟩ ⟨s.gpr .r8, 8 * 234⟩ :=
    psub (n := 8 * v.H.W) (k := 8 * 234) _ (by omega)
  have stk : below (u.gpr .rsp) 24 = ⟨s.gpr .rsp - 24, 24⟩ := by rw [hu.rsp]; rfl
  exact {
    rdi := hu.gpr _ (by decide), rsi := hu.gpr _ (by decide), rdx := hu.gpr _ (by decide)
    rcx := by rw [hu.gpr _ (by decide)]
    r8 := hu.gpr _ (by decide)
    klB := by rw [hB]; exact hkl'
    cr := by rw [hu.rd, hu.wr, hrd]; exact Covers.left (Covers.refl _)
    cw := by
      rw [hu.wr, hwr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact covers_pre hS192 (by simp)
        · exact covers_pre hS192 (by simp)
        · exact covers_pre (n := 8 * v.H.W) (k := 8 * 234) (by omega) (by simp)
    i_o := (i_o.sub_left si).sub_right so
    i_s := (i_s.sub_left si).sub_right ss
    o_s := (o_s.sub_left so).sub_right ss
    k_i := k_i.sub_right si
    k_o := k_o.sub_right so
    k_s := k_s.sub_right ss
    stk_i := by rw [stk]; exact t_i.sub_right si
    stk_o := by rw [stk]; exact t_o.sub_right so
    stk_k := by rw [stk]; exact t_k
    stk_s := by rw [stk]; exact t_s.sub_right ss
    scnw := by omega }

theorem init_case_wp {s u : State} (hs : initA.pre s) (hu : AtCase s u) {k : Nat} {v : MdHash} (hm : (k, v) ∈ vs)
    (hk : (s.gpr .r9).toNat = k) :
    WP isa (.call v.H.hmacInitN v.H.hmacInit) u fun s' => gprPreserved s s' ∧ initA.post s s' := by
  have hsat : ∃ t, (Spec.Hmac.initScratchContract v.ok.SH v.H.W X86_64.abi 16).pre t := by
    rw [v.hSH, v.hW]; exact v.hmacInit.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, r_i, r_o, r_s, -⟩ := id hs
  obtain ⟨-, hS192, hW, -, -, -⟩ := sizes G hm
  refine hinit_call v.ok (hmacInit_ok v.ok v.C v.K hsat) (nosp_of (core_hmacInit v.K.cNs v.K.iNs v.C.hinitNs))
    (core_hmacInit_depth v.K.cD v.K.iD v.C.hinitD) (init_args G hs hu hm hk) fun s' _ _ h₃ h₄ q₁ q₂ => ?_
  refine ⟨⟨fun r hr => by rw [h₃ r hr, hu.gpr r (rax_notCs hr)], ?_⟩, fun I hI => ?_⟩
  · rw [hu.mem, hu.rsp] at h₄
    refine ret_kept (by decide) h₄ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact r_i.sub_right (psub _ hS192)
    · exact r_o.sub_right (psub _ hS192)
    · exact r_s.sub_right (psub (n := 8 * v.H.W) (k := 8 * 234) _ (by omega))
  · have hI' : I = v.I := by
      rw [hk, G.inst k v hm] at hI; exact (Option.some.inj hI).symm
    subst hI'
    rw [hu.mem] at q₁ q₂
    rw [← v.hSH]
    exact ⟨q₁, q₂⟩

theorem init_wp (s : State) (hs : initA.pre s) :
    WP isa (Impl.Hmac.Any.X86_64.init (hsOf vs)) s fun s' => gprPreserved s s' ∧ initA.post s s' := by
  refine WP.seq (WP.mono (ldSel_wp s) fun s₁ h₁ => ?_)
  subst h₁
  refine Proof.Dispatch.chain_wp Proof.Dispatch.X86_64.tests _ (by rw [keys_map G _ fun _ => rfl]; exact keys_lt)
    (by rw [sel_ld, keys_map G _ fun _ => rfl]; exact hs.1.1) (by rw [keys_map G _ fun _ => rfl]; exact keys_nodup) fun c hc u hf _ => ?_
  rw [sel_ld] at hc
  obtain ⟨v, hm, e⟩ := mem_map (fun _ => rfl) hc
  cases e
  exact init_case_wp G hs (AtCase.of rfl hf) hm rfl

omit G in
theorem init_mx : (Impl.Hmac.Any.X86_64.init (hsOf vs)).allInstrs (fun i => !loadsMxcsr i) = true := by
  show ((Code.block ldSel : Prog isa).allInstrs _ && (Impl.Dispatch.X86_64.chain _).allInstrs _) = true
  rw [ldSel_mx, Bool.true_and]
  refine Proof.Dispatch.chain_allInstrs (M := isa) _ test_mx _ fun c hc => ?_
  obtain ⟨v, -, e⟩ := mem_map (k := c.1) (c := c.2) (fun _ => rfl) hc
  rw [← show (c.1, Code.call v.H.hmacInitN v.H.hmacInit).2 = c.2 from congrArg Prod.snd e]
  exact core_hmacInit v.K.cMx v.K.iMx v.C.hinitMx

theorem init_ct : ConstantTime isa initA.pre initA.pub (Impl.Hmac.Any.X86_64.init (hsOf vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq (ldSel_rel _) ?_)
  refine Proof.Dispatch.chain_relCT Proof.Dispatch.X86_64.tests (by rw [keys_map G _ fun _ => rfl]; exact keys_lt)
    (by rw [keys_map G _ fun _ => rfl]; exact keys_nodup) ?_ fun k c hc => ?_
  · rintro s₁ s₂ ⟨a₁, a₂, ⟨h₁, -, hp⟩, rfl, rfl⟩
    rw [sel_ld, sel_ld, hp.2.2.2.2.2.1, keys_map G _ fun _ => rfl]
    exact ⟨rfl, hp.2.2.2.2.2.1 ▸ h₁.1.1⟩
  · obtain ⟨v, hm, e⟩ := mem_map (fun _ => rfl) hc
    cases e
    have hsat : ∃ t, (Spec.Hmac.initScratchContract v.ok.SH v.H.W X86_64.abi 16).pre t := by
      rw [v.hSH, v.hW]; exact v.hmacInit.2.2
    refine RelCT.mono (RelCT.exists_ (α := Addr × Addr × Addr × Addr × Nat) fun x =>
      hinit_rel v.ok (hmacInit_ok v.ok v.C v.K hsat) (inn := x.1) (out := x.2.1) (k := x.2.2.1) (sc := x.2.2.2.1)
        (kl := x.2.2.2.2) (P := fun s s' => InitArgs (H := v.H) s x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 ∧
          InitArgs (H := v.H) s' x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 ∧ s.gpr .rsp = s'.gpr .rsp) fun _ _ h => h)
      ?_ fun _ _ _ => trivial
    rintro s₁ s₂ ⟨b₁, b₂, ⟨a₁, a₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, hk, f₁, f₂, -, -⟩
    rw [sel_ld] at hk
    obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hp
    have u₁ := AtCase.of rfl f₁
    have u₂ := AtCase.of rfl f₂
    refine ⟨(a₁.gpr .rdi, a₁.gpr .rsi, a₁.gpr .rdx, a₁.gpr .r8, (a₁.gpr .rcx).toNat),
      init_args G h₁ u₁ hm hk, ?_, u₁.rsp.trans (p7.trans u₂.rsp.symm)⟩
    rw [p1, p2, p3, p4, p5]
    exact init_args G h₂ u₂ hm (p6 ▸ hk)

theorem init_verified : Verified X86_64.target (Impl.Hmac.Any.X86_64.init (hsOf vs)) initA :=
  ⟨fun s hs => by
    obtain ⟨t, s', he, hg, hp⟩ := init_wp G s hs
    exact ⟨t, s', he, abiPreserved_of_exec init_mx he hg, hp⟩,
   init_ct G, initImp.sat_left⟩

end Init

/-! ## `update` -/

section Update

variable {vs : List (Nat × MdHash)} (G : Good vs)
include G

theorem upd_wb {k : Nat} {v : MdHash} (hm : (k, v) ∈ vs) : v.ok.stream.Wb ≤ 8 * 234 := by
  obtain ⟨-, -, hW, -, -, -⟩ := sizes G hm
  have := v.ok.fits
  show v.H.P.so + 48 ≤ 8 * 234
  omega

theorem upd_args {s u : State} (hs : updA.pre s) (hu : AtCase s u) {k : Nat} {v : MdHash} (hm : (k, v) ∈ vs) :
    Calls.UpdArgs v.ok.stream u (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .rcx).toNat := by
  obtain ⟨-, hrd, hwr, st_sc, d_st, d_sc, -, -, t_st, t_d, t_sc⟩ := hs
  obtain ⟨-, hS192, -, -, -, -⟩ := sizes G hm
  have hwb := upd_wb G hm
  have si : Region.Sub ⟨s.gpr .rdi, v.H.S⟩ ⟨s.gpr .rdi, 192⟩ := psub _ hS192
  have ss : Region.Sub ⟨s.gpr .r8, v.ok.stream.Wb⟩ ⟨s.gpr .r8, 8 * 234⟩ :=
    psub (n := v.ok.stream.Wb) (k := 8 * 234) _ hwb
  have stk : below (u.gpr .rsp) 16 = ⟨s.gpr .rsp - 16, 16⟩ := by rw [hu.rsp]; rfl
  exact {
    rdi := hu.gpr _ (by decide), rdx := hu.gpr _ (by decide)
    rcx := by rw [hu.gpr _ (by decide)]
    r8 := hu.gpr _ (by decide)
    cd := by rw [hu.rd, hu.wr, hrd]; exact Covers.left (Covers.refl _)
    cw := by
      rw [hu.wr, hwr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact covers_pre (n := v.H.S) hS192 (by simp)
        · exact covers_pre (n := v.ok.stream.Wb) (k := 8 * 234) hwb (by simp)
    st_sc := (st_sc.sub_left si).sub_right ss
    d_st := d_st.sub_right si
    d_sc := d_sc.sub_right ss
    stk_st := by rw [stk]; exact t_st.sub_right si
    stk_d := by rw [stk]; exact t_d
    stk_sc := by rw [stk]; exact t_sc.sub_right ss }

theorem upd_case_wp {s u : State} (hs : updA.pre s) (hu : AtCase s u) {k : Nat} {v : MdHash} (hm : (k, v) ∈ vs)
    (hk : (s.gpr .r9).toNat = k) :
    WP isa (.call v.H.updN v.H.updC) u fun s' => gprPreserved s s' ∧ updA.post s s' := by
  obtain ⟨-, -, -, -, -, -, r_st, r_sc, -⟩ := id hs
  obtain ⟨-, hS192, -, -, -, -⟩ := sizes G hm
  have hwb := upd_wb G hm
  refine Calls.upd_call v.ok.stream (upd_args G hs hu hm) (Nat.le_of_lt (BitVec.isLt _)) fun s' A hr => ?_
  refine ⟨⟨fun r hr' => by rw [A.cs r hr', hu.gpr r (rax_notCs hr')], ?_⟩, fun I hI => ?_⟩
  · have h₄ := A.frame
    rw [hu.mem, hu.rsp] at h₄
    refine ret_kept (by decide) h₄ fun r hr' => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact r_st.sub_right (psub _ hS192)
    · exact r_sc.sub_right (psub (n := v.ok.stream.Wb) (k := 8 * 234) _ hwb)
  · have hI' : I = v.I := by
      rw [hk, G.inst k v hm] at hI; exact (Option.some.inj hI).symm
    subst hI'
    intro msg hmsg hc
    rw [← v.hSH] at hmsg ⊢
    have := hr msg (by rw [hu.mem]; exact hmsg) (by rw [hu.gpr _ (by decide)]; exact hc)
    rw [hu.mem] at this
    exact this

theorem upd_wp (s : State) (hs : updA.pre s) :
    WP isa (Impl.Hmac.Any.X86_64.update (hsOf vs)) s fun s' => gprPreserved s s' ∧ updA.post s s' := by
  refine WP.seq (WP.mono (ldSel_wp s) fun s₁ h₁ => ?_)
  subst h₁
  refine Proof.Dispatch.chain_wp Proof.Dispatch.X86_64.tests _ (by rw [keys_map G _ fun _ => rfl]; exact keys_lt)
    (by rw [sel_ld, keys_map G _ fun _ => rfl]; exact hs.1) (by rw [keys_map G _ fun _ => rfl]; exact keys_nodup)
    fun c hc u hf _ => ?_
  rw [sel_ld] at hc
  obtain ⟨v, hm, e⟩ := mem_map (fun _ => rfl) hc
  cases e
  exact upd_case_wp G hs (AtCase.of rfl hf) hm rfl

omit G in
theorem upd_mx : (Impl.Hmac.Any.X86_64.update (hsOf vs)).allInstrs (fun i => !loadsMxcsr i) = true := by
  show ((Code.block ldSel : Prog isa).allInstrs _ && (Impl.Dispatch.X86_64.chain _).allInstrs _) = true
  rw [ldSel_mx, Bool.true_and]
  refine Proof.Dispatch.chain_allInstrs (M := isa) _ test_mx _ fun c hc => ?_
  obtain ⟨v, -, e⟩ := mem_map (k := c.1) (c := c.2) (fun _ => rfl) hc
  rw [← show (c.1, Code.call v.H.updN v.H.updC).2 = c.2 from congrArg Prod.snd e]
  exact v.K.updMx v.C

theorem upd_ct : ConstantTime isa updA.pre updA.pub (Impl.Hmac.Any.X86_64.update (hsOf vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq (ldSel_rel _) ?_)
  refine Proof.Dispatch.chain_relCT Proof.Dispatch.X86_64.tests (by rw [keys_map G _ fun _ => rfl]; exact keys_lt)
    (by rw [keys_map G _ fun _ => rfl]; exact keys_nodup) ?_ fun k c hc => ?_
  · rintro s₁ s₂ ⟨a₁, a₂, ⟨h₁, -, hp⟩, rfl, rfl⟩
    rw [sel_ld, sel_ld, hp.2.2.2.2.2.1, keys_map G _ fun _ => rfl]
    exact ⟨rfl, hp.2.2.2.2.2.1 ▸ h₁.1⟩
  · obtain ⟨v, hm, e⟩ := mem_map (fun _ => rfl) hc
    cases e
    refine RelCT.mono (RelCT.exists_ (α := Addr × Addr × Addr × Nat) fun x =>
      Calls.upd_rel v.ok.stream (st := x.1) (d := x.2.1) (sc := x.2.2.1) (len := x.2.2.2)
        (P := fun s s' => Calls.UpdArgs v.ok.stream s x.1 x.2.1 x.2.2.1 x.2.2.2 ∧
          Calls.UpdArgs v.ok.stream s' x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ s.gpr .rsi = s'.gpr .rsi ∧
          s.gpr .rsp = s'.gpr .rsp) fun _ _ h => h)
      ?_ fun _ _ _ => trivial
    rintro s₁ s₂ ⟨b₁, b₂, ⟨a₁, a₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, -, f₁, f₂, -, -⟩
    obtain ⟨p1, p2, p3, p4, p5, -, p7⟩ := hp
    have u₁ := AtCase.of rfl f₁
    have u₂ := AtCase.of rfl f₂
    refine ⟨(a₁.gpr .rdi, a₁.gpr .rdx, a₁.gpr .r8, (a₁.gpr .rcx).toNat), upd_args G h₁ u₁ hm, ?_,
      (u₁.gpr _ (by decide)).trans (p2.trans (u₂.gpr _ (by decide)).symm), u₁.rsp.trans (p7.trans u₂.rsp.symm)⟩
    rw [p1, p3, p4, p5]
    exact upd_args G h₂ u₂ hm

theorem upd_verified : Verified X86_64.target (Impl.Hmac.Any.X86_64.update (hsOf vs)) updA :=
  ⟨fun s hs => by
    obtain ⟨t, s', he, hg, hp⟩ := upd_wp G s hs
    exact ⟨t, s', he, abiPreserved_of_exec upd_mx he hg, hp⟩,
   upd_ct G, updImp.sat_left⟩

end Update

/-! ## `finalize` -/

section Fin

variable {vs : List (Nat × MdHash)} (G : Good vs)
include G

theorem fin_args {s u : State} (hs : finA.pre s) (hu : AtCase s u) {k : Nat} {v : MdHash} (hm : (k, v) ∈ vs) :
    FinArgs (H := v.H) u (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) := by
  obtain ⟨-, hrd, hwr, i_u, i_o, i_s, u_o, u_s, o_s, -, -, -, -, t_i, t_u, t_o, t_s, hsc⟩ := hs
  obtain ⟨-, hS192, hW, hD64, -, -⟩ := sizes G hm
  have si : Region.Sub ⟨s.gpr .rdi, v.H.S⟩ ⟨s.gpr .rdi, 192⟩ := psub _ hS192
  have su : Region.Sub ⟨s.gpr .rsi, v.H.S⟩ ⟨s.gpr .rsi, 192⟩ := psub _ hS192
  have so : Region.Sub ⟨s.gpr .rcx, v.H.D⟩ ⟨s.gpr .rcx, 64⟩ := psub _ hD64
  have ss : Region.Sub ⟨s.gpr .r8, 8 * v.H.W⟩ ⟨s.gpr .r8, 8 * 234⟩ :=
    psub (n := 8 * v.H.W) (k := 8 * 234) _ (by omega)
  have stk : below (u.gpr .rsp) 24 = ⟨s.gpr .rsp - 24, 24⟩ := by rw [hu.rsp]; rfl
  exact {
    rdi := hu.gpr _ (by decide), rsi := hu.gpr _ (by decide), rdx := hu.gpr _ (by decide)
    rcx := hu.gpr _ (by decide), r8 := hu.gpr _ (by decide)
    cr := by
      rw [hu.rd, hu.wr, hrd]
      exact Covers.left (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact covers_pre hS192 (by simp))
    cw := by
      rw [hu.wr, hwr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact covers_pre hS192 (by simp)
        · exact covers_pre hD64 (by simp)
        · exact covers_pre (n := 8 * v.H.W) (k := 8 * 234) (by omega) (by simp)
    i_u := (i_u.sub_left si).sub_right su
    i_o := (i_o.sub_left si).sub_right so
    i_s := (i_s.sub_left si).sub_right ss
    u_o := (u_o.sub_left su).sub_right so
    u_s := (u_s.sub_left su).sub_right ss
    o_s := (o_s.sub_left so).sub_right ss
    stk_i := by rw [stk]; exact t_i.sub_right si
    stk_u := by rw [stk]; exact t_u.sub_right su
    stk_o := by rw [stk]; exact t_o.sub_right so
    stk_s := by rw [stk]; exact t_s.sub_right ss
    scnw := by omega }

theorem fin_case_wp {s u : State} (hs : finA.pre s) (hu : AtCase s u) {k : Nat} {v : MdHash} (hm : (k, v) ∈ vs)
    (hk : (s.gpr .r9).toNat = k) :
    WP isa (.call v.H.hmacFinN v.H.hmacFin) u fun s' => gprPreserved s s' ∧ finA.post s s' := by
  have hsat : ∃ t, (Spec.Hmac.finalizeScratchContract v.ok.SH v.H.W X86_64.abi 16).pre t := by
    rw [v.hSH, v.hW]; exact v.hmacFin.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, r_i, -, r_o, r_s, -⟩ := id hs
  obtain ⟨-, hS192, hW, hD64, -, -⟩ := sizes G hm
  refine hfin_call v.ok (hmacFin_ok v.ok v.C v.K hsat) (nosp_of (core_hmacFin v.K.cNs v.C.hfinNs))
    (core_hmacFin_depth v.K.cD v.C.hfinD) (fin_args G hs hu hm) fun s' _ _ h₃ h₄ q => ?_
  refine ⟨⟨fun r hr => by rw [h₃ r hr, hu.gpr r (rax_notCs hr)], ?_⟩, fun I hI => ?_⟩
  · rw [hu.mem, hu.rsp] at h₄
    refine ret_kept (by decide) h₄ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact r_i.sub_right (psub _ hS192)
    · exact r_o.sub_right (psub _ hD64)
    · exact r_s.sub_right (psub (n := 8 * v.H.W) (k := 8 * 234) _ (by omega))
  · have hI' : I = v.I := by
      rw [hk, G.inst k v hm] at hI; exact (Option.some.inj hI).symm
    subst hI'
    intro k0 text hk0 hl hi hc ho
    have hB := v.ok.hB
    have hD := v.ok.hD
    rw [← v.hSH] at hk0 hi hc ho ⊢
    rw [hD]
    rw [hB] at hk0 hc
    exact q k0 text hk0 hl (by rw [hu.mem]; exact hi) hc (by rw [hu.mem]; exact ho)

theorem fin_wp (s : State) (hs : finA.pre s) :
    WP isa (Impl.Hmac.Any.X86_64.finalize (hsOf vs)) s fun s' => gprPreserved s s' ∧ finA.post s s' := by
  refine WP.seq (WP.mono (ldSel_wp s) fun s₁ h₁ => ?_)
  subst h₁
  refine Proof.Dispatch.chain_wp Proof.Dispatch.X86_64.tests _ (by rw [keys_map G _ fun _ => rfl]; exact keys_lt)
    (by rw [sel_ld, keys_map G _ fun _ => rfl]; exact hs.1) (by rw [keys_map G _ fun _ => rfl]; exact keys_nodup)
    fun c hc u hf _ => ?_
  rw [sel_ld] at hc
  obtain ⟨v, hm, e⟩ := mem_map (fun _ => rfl) hc
  cases e
  exact fin_case_wp G hs (AtCase.of rfl hf) hm rfl

omit G in
theorem fin_mx : (Impl.Hmac.Any.X86_64.finalize (hsOf vs)).allInstrs (fun i => !loadsMxcsr i) = true := by
  show ((Code.block ldSel : Prog isa).allInstrs _ && (Impl.Dispatch.X86_64.chain _).allInstrs _) = true
  rw [ldSel_mx, Bool.true_and]
  refine Proof.Dispatch.chain_allInstrs (M := isa) _ test_mx _ fun c hc => ?_
  obtain ⟨v, -, e⟩ := mem_map (k := c.1) (c := c.2) (fun _ => rfl) hc
  rw [← show (c.1, Code.call v.H.hmacFinN v.H.hmacFin).2 = c.2 from congrArg Prod.snd e]
  exact core_hmacFin v.K.cMx v.C.hfinMx

theorem fin_ct : ConstantTime isa finA.pre finA.pub (Impl.Hmac.Any.X86_64.finalize (hsOf vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq (ldSel_rel _) ?_)
  refine Proof.Dispatch.chain_relCT Proof.Dispatch.X86_64.tests (by rw [keys_map G _ fun _ => rfl]; exact keys_lt)
    (by rw [keys_map G _ fun _ => rfl]; exact keys_nodup) ?_ fun k c hc => ?_
  · rintro s₁ s₂ ⟨a₁, a₂, ⟨h₁, -, hp⟩, rfl, rfl⟩
    rw [sel_ld, sel_ld, hp.2.2.2.2.2.1, keys_map G _ fun _ => rfl]
    exact ⟨rfl, hp.2.2.2.2.2.1 ▸ h₁.1⟩
  · obtain ⟨v, hm, e⟩ := mem_map (fun _ => rfl) hc
    cases e
    have hsat : ∃ t, (Spec.Hmac.finalizeScratchContract v.ok.SH v.H.W X86_64.abi 16).pre t := by
      rw [v.hSH, v.hW]; exact v.hmacFin.2.2
    refine RelCT.mono (RelCT.exists_ (α := Addr × Addr × Addr × Addr × Addr) fun x =>
      hfin_rel v.ok (hmacFin_ok v.ok v.C v.K hsat) (inn := x.1) (outer := x.2.1) (cnt := x.2.2.1)
        (o := x.2.2.2.1) (sc := x.2.2.2.2) (P := fun s s' => FinArgs (H := v.H) s x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 ∧
          FinArgs (H := v.H) s' x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 ∧ s.gpr .rsp = s'.gpr .rsp) fun _ _ h => h)
      ?_ fun _ _ _ => trivial
    rintro s₁ s₂ ⟨b₁, b₂, ⟨a₁, a₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, -, f₁, f₂, -, -⟩
    obtain ⟨p1, p2, p3, p4, p5, -, p7⟩ := hp
    have u₁ := AtCase.of rfl f₁
    have u₂ := AtCase.of rfl f₂
    refine ⟨(a₁.gpr .rdi, a₁.gpr .rsi, a₁.gpr .rdx, a₁.gpr .rcx, a₁.gpr .r8), fin_args G h₁ u₁ hm, ?_,
      u₁.rsp.trans (p7.trans u₂.rsp.symm)⟩
    rw [p1, p2, p3, p4, p5]
    exact fin_args G h₂ u₂ hm

theorem fin_verified : Verified X86_64.target (Impl.Hmac.Any.X86_64.finalize (hsOf vs)) finA :=
  ⟨fun s hs => by
    obtain ⟨t, s', he, hg, hp⟩ := fin_wp G s hs
    exact ⟨t, s', he, abiPreserved_of_exec fin_mx he hg, hp⟩,
   fin_ct G, finImp.sat_left⟩

end Fin

/-! ## The stack pointer -/

/-- An instruction that does not clobber `rsp` (`Taint.clobbers`, which the
kernel checks of the hash functions' code) does not write it. -/
theorem writesSp_of_clobbers (i : Instr) (h : Taint.clobbers i .rsp = false) : isa.writesSp i = false := by
  cases i <;> simp_all [Taint.clobbers, Taint.dstOf, Instr.dst] <;> grind

theorem all_sp_of_ns {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) :
    c.all (fun i => !isa.writesSp i) = true := by
  refine Code.all_of_allInstrs ?_
  rw [Code.allInstrs_eq, List.all_eq_true] at h ⊢
  intro i hi
  have := h i hi
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at this
  rw [writesSp_of_clobbers i this]; rfl

theorem ldSel_sp : (Code.block ldSel : Prog isa).all (fun i => !isa.writesSp i) = true := by decide

theorem test_sp (k : Nat) :
    (Impl.Dispatch.X86_64.test k).all (fun i => !isa.writesSp i) = true := rfl

theorem init_sp (vs : List (Nat × MdHash)) :
    (Impl.Hmac.Any.X86_64.init (hsOf vs)).all (fun i => !isa.writesSp i) = true := by
  show ((Code.block ldSel : Prog isa).all _ && (Impl.Dispatch.X86_64.chain _).all _) = true
  rw [ldSel_sp, Bool.true_and]
  refine Proof.Dispatch.chain_all (M := isa) _ test_sp _ fun c hc => ?_
  obtain ⟨v, -, e⟩ := mem_map (k := c.1) (c := c.2) (fun _ => rfl) hc
  rw [← show (c.1, Code.call v.H.hmacInitN v.H.hmacInit).2 = c.2 from congrArg Prod.snd e]
  exact v.hmacInitSp

theorem upd_sp (vs : List (Nat × MdHash)) :
    (Impl.Hmac.Any.X86_64.update (hsOf vs)).all (fun i => !isa.writesSp i) = true := by
  show ((Code.block ldSel : Prog isa).all _ && (Impl.Dispatch.X86_64.chain _).all _) = true
  rw [ldSel_sp, Bool.true_and]
  refine Proof.Dispatch.chain_all (M := isa) _ test_sp _ fun c hc => ?_
  obtain ⟨v, -, e⟩ := mem_map (k := c.1) (c := c.2) (fun _ => rfl) hc
  rw [← show (c.1, Code.call v.H.updN v.H.updC).2 = c.2 from congrArg Prod.snd e]
  exact all_sp_of_ns (core_updC v.K.cNs v.C.updNs)

theorem fin_sp (vs : List (Nat × MdHash)) :
    (Impl.Hmac.Any.X86_64.finalize (hsOf vs)).all (fun i => !isa.writesSp i) = true := by
  show ((Code.block ldSel : Prog isa).all _ && (Impl.Dispatch.X86_64.chain _).all _) = true
  rw [ldSel_sp, Bool.true_and]
  refine Proof.Dispatch.chain_all (M := isa) _ test_sp _ fun c hc => ?_
  obtain ⟨v, -, e⟩ := mem_map (k := c.1) (c := c.2) (fun _ => rfl) hc
  rw [← show (c.1, Code.call v.H.hmacFinN v.H.hmacFin).2 = c.2 from congrArg Prod.snd e]
  exact v.hmacFinSp

/-! ## A tier -/

/-- The hash functions of the tier `t` that these functions take, by number. -/
def vsOf (t : Tier) : List (Nat × MdHash) := hashIds.filterMap fun i => (t.get i).map fun v => (i, v)

theorem tier_length (t : Tier) : t.hashes.length = 8 := by
  simpa using congrArg List.length t.mgf_ok

theorem good (t : Tier) : Good (vsOf t) where
  keys := by
    have h := tier_length t
    have hi := t.insts
    unfold vsOf Tier.get
    generalize t.hashes = l at h hi ⊢
    rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [List.length_cons, List.length_nil] at h <;> try omega
    simp [hashIds]
  inst k v hm := by
    have hi := t.insts
    unfold vsOf Tier.get at hm
    simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at hm
    obtain ⟨i, hk, v', hv, rfl, rfl⟩ := hm
    have e := congrArg (·[i]?) hi
    simp only [List.getElem?_map, hv, Option.map_some] at e
    simp only [hashIds, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at e <;>
      simp [inst, e]

/-! ## Against the shared contracts -/

/-- `vg_hmac_init_scratch` of the tier `t`. -/
theorem init_spec (t : Tier) : Verified X86_64.target (Impl.Hmac.Any.X86_64.init (hsOf (vsOf t)))
    (Spec.Hmac.Any.initContract X86_64.abi 24) :=
  (init_verified (good t)).of_implies initImp

/-- `vg_hash_update_scratch` of the tier `t`. -/
theorem upd_spec (t : Tier) : Verified X86_64.target (Impl.Hmac.Any.X86_64.update (hsOf (vsOf t)))
    (Spec.Hmac.Any.updateContract X86_64.abi 16) :=
  (upd_verified (good t)).of_implies updImp

/-- `vg_hmac_finalize_scratch` of the tier `t`. -/
theorem fin_spec (t : Tier) : Verified X86_64.target (Impl.Hmac.Any.X86_64.finalize (hsOf (vsOf t)))
    (Spec.Hmac.Any.finalizeContract X86_64.abi 24) :=
  (fin_verified (good t)).of_implies finImp

end VG.Proof.Hmac.Any.X86_64
