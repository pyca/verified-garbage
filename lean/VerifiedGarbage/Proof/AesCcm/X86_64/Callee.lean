import VerifiedGarbage.Proof.AesCcm.X86_64.Env
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call
import VerifiedGarbage.Proof.Aes.X86_64.Variant
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-!
# AES-CCM on x86-64: the functions called

Untrusted: everything here is checked by Lean. A call of `vg_aes_ctr32`
from its contract (with `WP.call`): what it needs (`CtrCall`), what it
leaves (`CtrPost`), and that two calls with the same arguments leak the same
(`ctr_rel`); the calls of `vg_cmac_aes_update` are those of streaming
AES-CMAC (`Proof.CmacAes.Stream.X86_64.upd_call`). `uargs` and `cargs` build
their arguments from the environment: the key schedule, a block of `W` as
the state or the counter block, the data or blocks of `W` as the data, and
the working space at `W + 384`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctr32 aesWith)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.Stream.X86_64 (UArgs)

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  rw [blockAt, blockAt, bytesAt_frame hf hd (by decide)]

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    blocksAt m' p n = blocksAt m p n := by
  rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, bytesAt_frame hf hd hn]

/-- The cipher of a key schedule outside a frame's regions. -/
theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Ccm.ctxCiph m' K R = Spec.Ccm.ctxCiph m K R := by
  unfold Spec.Ccm.ctxCiph
  rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega)]

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem disj_below {s : State} {p : Addr} {n : Nat} (h : (below (s.gpr .rsp) 8).Disjoint ⟨p, n⟩) :
    ∀ r ∈ [below (s.gpr .rsp) 8], (⟨p, n⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.symm

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R :=
  toNat_ofNat_of_lt (by omega)

theorem below8_sub (sp : Addr) : Region.Sub (below sp 8) (below sp 16) :=
  Offset.sub_below sp (a := 8) (b := 16) (by decide) (by decide)

/-! ## `vg_aes_ctr32` -/

/-- What a call of `vg_aes_ctr32` needs: the key schedule at `K` for `R`
rounds, the counter block at `C`, `n` blocks at `D` and working space at `S`. -/
structure CtrCall (s : State) (K C D S : Addr) (R n : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = D
  r8 : s.gpr .r8 = BitVec.ofNat 64 n
  r9 : s.gpr .r9 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  kc : (⟨K, 240⟩ : Region).Disjoint ⟨C, 16⟩
  kd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ks : (⟨K, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2048⟩
  stkK : (below (s.gpr .rsp) 8).Disjoint ⟨K, 240⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 16⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 16 * n⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 2048⟩
  reads : Covers ([⟨K, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] s.wr

/-- What a call of `vg_aes_ctr32` leaves. -/
structure CtrPost (s : State) (K C D S : Addr) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : blocksAt s'.mem D n = ctr32 (aesWith R (bytesAt s.mem K (16 * (R + 1)))) (blockAt s.mem C)
    (blocksAt s.mem D n)

theorem CtrCall.pre {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    Proof.Aes.ctr32X86_64.pre
      (s.callEntry.withRegions [⟨K, 240⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_of_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  simp only [Proof.Aes.ctr32X86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR, hn]
  exact ⟨trivial, trivial, h.kc, h.kd, h.ks, h.cd, h.cs, h.ds, h.stkC, h.stkD, h.stkS, h.wrap,
    h.rounds⟩

theorem ctr_call (v : Ctr32Impl) {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    WP isa (.call v.callee.name v.callee.code) s (CtrPost s K C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_of_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  refine WP.call (k := Proof.Aes.ctr32X86_64) v.ok v.nosp (by rw [v.depth]; decide)
    (rd := [⟨K, 240⟩]) (wr := [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [v.depth] at hf
  obtain ⟨hdata, _⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hn,
    hm₂] at hdata
  have fE := callEntry_frame s
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with rfl | rfl | rfl <;> decide
  have eK := bytesAt_frame fE (p := K) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stkK.sub_right (Region.sub_prefix hRb)).symm) (by omega)
  rw [blockAt_frame fE (disj_below h.stkC), blocksAt_frame fE (disj_below h.stkD) (by have := h.wrap; omega),
    eK] at hdata
  exact ⟨hrd, hwr, hcs, by simpa using hf, hdata⟩

theorem ctr_rel (v : Ctr32Impl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C D S : Addr, ∃ R n : Nat,
      CtrCall s₁ K C D S R n ∧ CtrCall s₂ K C D S R n ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.callee.name v.callee.code) fun _ _ => True := by
  refine RelCT.callEx v.ok v.ct fun s₁ s₂ hp => ?_
  obtain ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.ctr32X86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## The arguments -/

/-- Data for a call: `k` bytes at `Q`, which the code may read, apart from
the parts of `W` from `384` on and the stack below `SP`. -/
structure Src (W SP : Addr) (s : State) (Q : Addr) (k : Nat) : Prop where
  rd : Covers [⟨Q, k⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + k ≤ 2 ^ 64
  qs : (⟨Q, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 384, 2176⟩
  stk : (below SP 16).Disjoint ⟨Q, k⟩

/-- Bytes of `W` below 384 as data. -/
theorem srcW {K W SP : Addr} {s : State} (L : Lay K W SP) (P : Perm K W s) {t k : Nat} (hk : t + k ≤ 384) :
    Src W SP s (W + BitVec.ofNat 64 t) k where
  rd := covers_left (P.wC (by omega))
  wrap := by
    have := L.ww
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := t) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  qs := L.w_w (.inl (by omega)) (by omega) (by decide)
  stk := L.stk_w' (by omega)

/-- A buffer as data. -/
theorem srcBuf {K W SP : Addr} {s : State} {Q : Addr} {k : Nat} (h : Buf K W SP s Q k) : Src W SP s Q k :=
  ⟨h.rd, h.wrap, h.w.sub_right (Lay.wSub (by decide)), h.stk⟩

/-- The arguments of `vg_cmac_aes_update`: the key schedule, the state at
`W + y`, `n` blocks at `Q`, and the working space at `W + 384`. -/
theorem uargs {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat} (hy : y + 16 ≤ 384) {Q : Addr} {n : Nat}
    (hq : Src W SP s Q (16 * n)) (hqy : (⟨Q, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩)
    (hn : 16 * n < 2 ^ 64) (rdi : s.gpr .rdi = K) (rsi : s.gpr .rsi = BitVec.ofNat 64 R) (rdx : s.gpr .rdx = W + BitVec.ofNat 64 y)
    (rcx : s.gpr .rcx = Q) (r8 : s.gpr .r8 = BitVec.ofNat 64 n) (r9 : s.gpr .r9 = W + BitVec.ofNat 64 384) :
    UArgs s K (W + BitVec.ofNat 64 y) Q (W + BitVec.ofNat 64 384) R n where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := hR
  hn := hn
  wc := by simpa using L.k_w' (a := 0) (n := 240) (d := y) (k := 16) (by decide) (by omega)
  ws := by simpa using L.k_w' (a := 0) (n := 240) (d := 384) (k := 2176) (by decide) (by decide)
  dc := hqy
  ds := hq.qs
  cs := L.w_w (.inl (by omega)) (by omega) (by decide)
  stkW := by rw [E.rsp]; exact L.stk_k
  stkD := by rw [E.rsp]; exact hq.stk
  stkC := by rw [E.rsp]; exact L.stk_w' (by omega)
  stkS := by rw [E.rsp]; exact L.stk_w' (by decide)
  wrapC := by
    have := L.ww
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := y) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  wrapD := hq.wrap
  wrapS := by
    have := L.ww
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 384) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  reads := covers_append (covers_cons E.perm.k (covers_cons hq.rd covers_nil))
    (covers_cons (covers_left (E.perm.wC (by omega))) (covers_cons (covers_left (E.perm.wC (by decide))) covers_nil))
  writes := covers_cons (E.perm.wC (by omega)) (covers_cons (E.perm.wC (by decide)) covers_nil)

/-- The arguments of `vg_aes_ctr32`: the key schedule, the counter block at
`W + c`, `n` blocks at `Q`, which it may write, and the working space at
`W + 384`. -/
theorem cargs {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {c : Nat} (hc : c + 16 ≤ 384) {Q : Addr} {n : Nat}
    (hq : Src W SP s Q (16 * n)) (hqc : (⟨Q, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 c, 16⟩)
    (hqk : (⟨K, 240⟩ : Region).Disjoint ⟨Q, 16 * n⟩) (hqw : Covers [⟨Q, 16 * n⟩] s.wr)
    (rdi : s.gpr .rdi = K) (rsi : s.gpr .rsi = BitVec.ofNat 64 R) (rdx : s.gpr .rdx = W + BitVec.ofNat 64 c)
    (rcx : s.gpr .rcx = Q) (r8 : s.gpr .r8 = BitVec.ofNat 64 n) (r9 : s.gpr .r9 = W + BitVec.ofNat 64 384) :
    CtrCall s K (W + BitVec.ofNat 64 c) Q (W + BitVec.ofNat 64 384) R n where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := hR
  wrap := hq.wrap
  kc := by simpa using L.k_w' (a := 0) (n := 240) (d := c) (k := 16) (by decide) (by omega)
  kd := hqk
  ks := by simpa using L.k_w' (a := 0) (n := 240) (d := 384) (k := 2048) (by decide) (by decide)
  cd := hqc.symm
  cs := L.w_w (.inl (by omega)) (by omega) (by decide)
  ds := hq.qs.sub_right (Region.sub_prefix (by decide))
  stkK := by rw [E.rsp]; exact L.stk_k.sub_left (below8_sub _)
  stkC := by rw [E.rsp]; exact (L.stk_w' (by omega)).sub_left (below8_sub _)
  stkD := by rw [E.rsp]; exact hq.stk.sub_left (below8_sub _)
  stkS := by rw [E.rsp]; exact (L.stk_w' (a := 384) (n := 2048) (by decide)).sub_left (below8_sub _)
  reads := covers_append (covers_cons E.perm.k covers_nil)
    (covers_cons (covers_left (E.perm.wC (by omega))) (covers_cons hq.rd
      (covers_cons (covers_left (E.perm.wC (by decide))) covers_nil)))
  writes := covers_cons (E.perm.wC (by omega)) (covers_cons hqw (covers_cons (E.perm.wC (by decide)) covers_nil))

end VG.Proof.AesCcm.X86_64
