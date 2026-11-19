module

public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTextSCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.SealLeaves
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenLeaves
public import VerifiedGarbage.Proof.Framework.X86_64.Leaves
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamClrVerified
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCryptCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM on x86-64: what `streamTextS` leaves in `W`

Untrusted: everything here is checked by Lean. With implementations of
`vg_aes_ctr32` and `vg_ghash` that never touch their working space, and a
blocks function that leaves in its `scratch` a function of its arguments
(`BlkLeft`), `streamTextS` leaves in `W` from byte 448 on what that
function says if it called it (at least 256 bytes), and else what was
there (`streamTextS_leaves`); and at `192`–`224` the lengths and the data's
address past what it did in the pieces before the rest. Each piece keeps
`W + 448` (`Keep448`): the additional data padded (`startS_keep`), the
head (`headPart_keep`) and the rest (`part_keep`); the whole blocks leave
what the function says (`blocks_leaves`).
-/

-- separate module: its one importer imports `Instances`, and with it every proof of AES-GCM on x86-64; these generic proofs need no re-checking when one of those changes

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom zeros padLen ghashInput)
open VG.Proof.Gcm (Absorbed Ctr)

/-- The bytes of `W` from 448 on, the blocks function's `scratch`, as they were. -/
abbrev Keep448 (W : Addr) (m m' : Mem) : Prop :=
  ∀ x, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 → m' x = m x

theorem Keep448.refl (W : Addr) (m : Mem) : Keep448 W m m := fun _ _ => rfl

theorem Keep448.trans {W : Addr} {m₁ m₂ m₃ : Mem} (h₁ : Keep448 W m₁ m₂) (h₂ : Keep448 W m₂ m₃) :
    Keep448 W m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Keep448.of_eq {W : Addr} {m₁ m₂ : Mem} (h : m₂ = m₁) : Keep448 W m₁ m₂ := fun _ _ => by rw [h]

theorem Keep448.of_frame {W : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Disjoint r) : Keep448 W m m' :=
  fun _ hx => frame_at hf hd hx

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

theorem k448_crFrameS {s : State} {Dj : Addr} {k : Nat} (hd : DataOk St W SP s Dj k) :
    ∀ r ∈ crFrameS St W SP Dj k 0, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.disj_empty
  · exact (L.stk_w (by decide)).symm

theorem k448_absFrame : ∀ r ∈ absFrame St W SP 16 0, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.disj_empty
  · exact (L.stk_w (by decide)).symm

theorem k448_sFrame : ∀ r ∈ sFrame St W SP 16 0, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.disj_empty
  · exact (L.stk_w (by decide)).symm

theorem k448_slots {d k : Nat} (h : d + k ≤ 448) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 d, k⟩ : Region)], (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact L.w_w (.inr h) (by decide) (by omega_arith)

end

/-- `absorb`'s output with no working space for `vg_ghash`, with all 256. -/
theorem AbsOut.of0 {Ctx St W SP : Addr} {yo : Nat} {H : Block} {x₀ x : List Byte} {m₀ : Mem} {s : State}
    (h : AbsOut Ctx St W SP yo H x₀ x m₀ s 2560 0) : AbsOut Ctx St W SP yo H x₀ x m₀ s :=
  ⟨h.env, h.abs, h.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨⟨St + BitVec.ofNat 64 32, 16⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 512, 256⟩, by simp, sub_empty⟩
    · exact ⟨below SP 8, by simp, fun _ h => h⟩⟩

/-! ## Callees that zero their working space -/

/-- The offsets from `a` to `b`. -/
def zw (a b : Nat) : Nat → Bool := fun d => decide (a ≤ d ∧ d < b)

/-- A call of a function whose code ends with `wipeX r 0 n`, after code
that never writes `r`, from a state whose `r` is in a region `u` may write:
the `n` bytes at `r` are zero on return. -/
theorem wipeR_zero {nm : String} {c : Prog isa} {r : Reg} {n b : Nat} (hb : b < 2 ^ 64) (hn : n ≤ b)
    (h16 : n % 16 = 0 ∨ 16 ≤ n) (hr : ∀ i ∈ instrs c, Taint.clobbers i r = false) (hrs : r ≠ .rsp)
    {s u : State} {t : List Leak} (e : Exec isa (.call nm (.seq c (.block (wipeX r 0 n)))) s t u)
    (hR : Covers [⟨s.gpr r, b⟩] s.wr) :
    ∀ x, (x - s.gpr r).toNat < n → u.mem x = 0 := by
  cases e with
  | call hc hb' hret =>
    rename_i s₁ s₂
    cases hb' with
    | seq a w =>
      cases w with
      | block w =>
        simp only [isa, call, Option.some.injEq] at hc
        subst hc
        obtain ⟨-, hwr⟩ := Exec.rdwr a
        obtain hg := Exec.gpr hr a
        rw [RegUpd.gpr_setReg_of_ne (h := hrs)] at hg
        obtain ⟨m', ew, hm⟩ := wipeX_run (o := 0) hb _ (by rw [hwr]; exact hR) hg (by omega) h16
        rw [ew] at w
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj w)
        simp only [isa, X86_64.ret] at hret
        split at hret <;> cases hret
        intro x hx
        show m' x = 0
        rw [hm x, Scrub.ite_t ⟨Nat.zero_le _, by omega⟩]

theorem CtrCall.preS {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    Proof.Aes.ctr32X86_64S.pre
      (s.callEntry.withRegions [⟨K, 240⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 1480⟩]) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.wrap; omega_using [this])
  obtain hs : Region.Sub ⟨S, 1480⟩ ⟨S, 2048⟩ := Region.sub_prefix (by decide)
  simp only [Proof.Aes.ctr32X86_64S, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR, hn]
  exact ⟨trivial, trivial, h.kc, h.kd, h.ks.sub_right hs, h.cd, h.cs.sub_right hs, h.ds.sub_right hs, h.stkC,
    h.stkD, h.stkS.sub_right hs, h.wrap, h.rounds⟩

theorem covers_1480 {rs rs' : List Region} {S : Addr} (h : Covers (rs ++ [⟨S, 2048⟩]) rs') :
    Covers (rs ++ [⟨S, 1480⟩]) rs' := fun a m ⟨r, hr, hc⟩ => by
  rcases List.mem_append.mp hr with hr | hr
  · exact h a m ⟨r, List.mem_append_left _ hr, hc⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact h a m ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by
      simp only [Region.Contains] at hc ⊢; omega⟩

/-- `ctr_call`, with an implementation that uses only 1480 bytes of its
working space (`Ctr32Small`). -/
theorem ctr_callS (v : Proof.Aes.X86_64.Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) {s : State}
    {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    WP isa (.call v.callee.name v.callee.code) s fun s' => CtrPost s K C D S R n s' ∧
      Frame [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 1480⟩, below (s.gpr .rsp) 8] s.mem s'.mem := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.wrap; omega_using [this])
  have hr := covers_1480 (rs := [⟨K, 240⟩, ⟨C, 16⟩, ⟨D, 16 * n⟩]) (by simpa using h.reads)
  have hw := covers_1480 (rs := [⟨C, 16⟩, ⟨D, 16 * n⟩]) (by simpa using h.writes)
  refine WP.call (k := Proof.Aes.ctr32X86_64S) f.ok v.nosp (by rw [v.depth]; decide)
    (rd := [⟨K, 240⟩]) (wr := [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 1480⟩]) h.preS (by simpa using hr) (by simpa using hw) ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [v.depth] at hf
  obtain ⟨hdata, hctr⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hn,
    hm₂] at hdata hctr
  have fE := callEntry_frame s
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with rfl | rfl | rfl <;> decide
  have eK := bytesAt_frame fE (p := K) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stkK.sub_right (Region.sub_prefix hRb)).symm) (by omega_using [hRb])
  rw [blockAt_frame fE (disj_below h.stkC), blocksAt_frame fE (disj_below h.stkD) (by have := h.wrap; omega_using [this]),
    eK] at hdata
  rw [blockAt_frame fE (disj_below h.stkC)] at hctr
  have hf' : Frame [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 1480⟩, below (s.gpr .rsp) 8] s.mem s'.mem := by simpa using hf
  exact ⟨⟨hrd, hwr, hcs, hf'.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨S, 2048⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩, hdata, hctr⟩, hf'⟩

/-- `vg_aes_ctr32` that zeroes the 1480 bytes of its working space before it
returns, used through its contract with 1480 bytes: what it leaves from
`W + 512`, its working space, is zero there. -/
theorem crCallZ_wipe (v : GcmImpl) {c₀ : Prog isa} (hc : v.ctr.callee.code = .seq c₀ (.block (wipeX .r9 0 1480)))
    (h9 : ∀ i ∈ instrs c₀, Taint.clobbers i .r9 = false) (f : Proof.Aes.X86_64.Ctr32Small v.ctr.callee) :
    CrCallZ v 1480 (zw 512 1992) := by
  intro s K C D W R n h
  obtain ⟨t, u, e, q, fr⟩ := ctr_callS v.ctr f h
  refine ⟨t, u, e, q, fr, fun d a b => ?_⟩
  rw [hc] at e
  obtain hR : Covers [⟨s.gpr .r9, 2048⟩] s.wr := fun a m ⟨r, hr, hcn⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h.r9] at hcn
    exact h.writes a m ⟨⟨W + BitVec.ofNat 64 512, 2048⟩, by simp, hcn⟩
  obtain e9 : s.gpr .r9 = W + BitVec.ofNat 64 512 := h.r9
  obtain hd : (W + BitVec.ofNat 64 d - s.gpr .r9).toNat = d - 512 := by
    rw [e9]; exact Offset.sub_toNat W a (by omega)
  by_cases hz : d < 1992
  · rw [show zw 512 1992 d = true by simp [zw]; omega, Scrub.ite_t rfl]
    exact wipeR_zero (by decide) (by decide) (.inr (by decide)) h9 (by decide) e hR _ (by rw [hd]; omega)
  · rw [show zw 512 1992 d = false by simp [zw]; omega]
    exact fr _ fun r hr hcn => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      obtain hS : (⟨W + BitVec.ofNat 64 512, 2048⟩ : Region).Contains (W + BitVec.ofNat 64 d) 1 := by
        show (W + BitVec.ofNat 64 d - (W + BitVec.ofNat 64 512)).toNat + 1 ≤ 2048
        rw [Offset.sub_toNat W a (by omega)]; omega
      rcases hr with rfl | rfl | rfl | rfl
      · exact h.cs _ hcn hS
      · exact h.ds _ hcn hS
      · simp only [Region.Contains] at hcn; rw [Offset.sub_toNat W a (by omega)] at hcn; omega
      · exact h.stkS _ hcn hS

/-- `wipeR_zero`, for a function that then clears the registers (`clrAfter`). -/
theorem wipeR_zeroC (lv : VG.Impl.Scrub.X86_64.VecLevel) {nm : String} {c : Prog isa} {r : Reg} {n b : Nat} (hb : b < 2 ^ 64) (hn : n ≤ b)
    (h16 : n % 16 = 0 ∨ 16 ≤ n) (hr : ∀ i ∈ instrs c, Taint.clobbers i r = false) (hrs : r ≠ .rsp)
    {s u : State} {t : List Leak}
    (e : Exec isa (.call nm (.seq (.seq c (.block (wipeX r 0 n))) (.block (clrAfter lv)))) s t u)
    (hR : Covers [⟨s.gpr r, b⟩] s.wr) :
    ∀ x, (x - s.gpr r).toNat < n → u.mem x = 0 := by
  cases e with
  | call hc hb' hret =>
    rename_i s₁ s₂
    cases hb' with
    | seq a w =>
      cases w with
      | block w =>
        rw [execBlock_clrAfter] at w
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj w)
        cases a with
        | seq a w₁ =>
          cases w₁ with
          | block w₁ =>
            simp only [isa, call, Option.some.injEq] at hc
            subst hc
            obtain ⟨-, hwr⟩ := Exec.rdwr a
            obtain hg := Exec.gpr hr a
            rw [RegUpd.gpr_setReg_of_ne (h := hrs)] at hg
            obtain ⟨m', ew, hm⟩ := wipeX_run (o := 0) hb _ (by rw [hwr]; exact hR) hg (by omega) h16
            rw [ew] at w₁
            obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj w₁)
            simp only [isa, X86_64.ret] at hret
            split at hret <;> cases hret
            intro x hx
            show m' x = 0
            rw [hm x, Scrub.ite_t ⟨Nat.zero_le _, by omega⟩]

/-- `crCallZ_wipe`, for the function clearing the registers too. -/
theorem crCallZ_wipeC (lv : VG.Impl.Scrub.X86_64.VecLevel) (v : GcmImpl) {c₀ : Prog isa}
    (hc : v.ctr.callee.code = .seq (.seq c₀ (.block (wipeX .r9 0 1480))) (.block (clrAfter lv)))
    (h9 : ∀ i ∈ instrs c₀, Taint.clobbers i .r9 = false) (f : Proof.Aes.X86_64.Ctr32Small v.ctr.callee) :
    CrCallZ v 1480 (zw 512 1992) := by
  intro s K C D W R n h
  obtain ⟨t, u, e, q, fr⟩ := ctr_callS v.ctr f h
  refine ⟨t, u, e, q, fr, fun d a b => ?_⟩
  rw [hc] at e
  obtain hR : Covers [⟨s.gpr .r9, 2048⟩] s.wr := fun a m ⟨r, hr, hcn⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h.r9] at hcn
    exact h.writes a m ⟨⟨W + BitVec.ofNat 64 512, 2048⟩, by simp, hcn⟩
  obtain e9 : s.gpr .r9 = W + BitVec.ofNat 64 512 := h.r9
  obtain hd : (W + BitVec.ofNat 64 d - s.gpr .r9).toNat = d - 512 := by
    rw [e9]; exact Offset.sub_toNat W a (by omega)
  by_cases hz : d < 1992
  · rw [show zw 512 1992 d = true by simp [zw]; omega, Scrub.ite_t rfl]
    exact wipeR_zeroC lv (by decide) (by decide) (.inr (by decide)) h9 (by decide) e hR _ (by rw [hd]; omega)
  · rw [show zw 512 1992 d = false by simp [zw]; omega]
    exact fr _ fun r hr hcn => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      obtain hS : (⟨W + BitVec.ofNat 64 512, 2048⟩ : Region).Contains (W + BitVec.ofNat 64 d) 1 := by
        show (W + BitVec.ofNat 64 d - (W + BitVec.ofNat 64 512)).toNat + 1 ≤ 2048
        rw [Offset.sub_toNat W a (by omega)]; omega
      rcases hr with rfl | rfl | rfl | rfl
      · exact h.cs _ hcn hS
      · exact h.ds _ hcn hS
      · simp only [Region.Contains] at hcn; rw [Offset.sub_toNat W a (by omega)] at hcn; omega
      · exact h.stkS _ hcn hS

/-- `vg_aes_ctr32` that needs no working space: it leaves `W + 512` as it was. -/
theorem crCallZ_free (v : GcmImpl) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) : CrCallZ v 0 zNo := by
  intro s K C D W R n h
  obtain ⟨t, u, e, q, fr⟩ := CrCallP.free v cf h
  refine ⟨t, u, e, q, fr, KeepZ.of_frame fr fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.cs.symm
  · exact h.ds.symm
  · exact Lay.disj_empty
  · exact h.stkS.symm

/-! ## `vg_ghash` zeroing its working space -/

/-- How the functions with 2560 bytes at `W` call `v`'s `vg_ghash`, with the
256 bytes of working space at `W + 512` (`GhFits.inst2560`): what it leaves
from `W + 512` (`KeepZ W z`). -/
def GhCallZ (v : GcmImpl) (z : Nat → Bool) : Prop :=
  ∀ {Ctx St W SP : Addr} {yo : Nat} {P : Addr} {n : Nat} {s : State}, Lay Ctx St W SP →
    (yo = 0 ∨ yo = 16) → GhArgs Ctx St W SP 2560 yo P n 256 s →
    WP isa (.call v.gh.fn.name v.gh.fn.code) s fun s' => KeepZ W z s.mem s'.mem

/-- `GhFits.ok`, with what `GhCallZ` says. -/
theorem GhCallZ.ok {v : GcmImpl} {z : Nat → Bool} (GZ : GhCallZ v z) {Ctx St W SP : Addr} {yo : Nat} {P : Addr}
    {n : Nat} {s : State} (L : Lay Ctx St W SP) (hyo : yo = 0 ∨ yo = 16) (h : GhArgs Ctx St W SP 2560 yo P n 256 s) :
    WP isa (.call v.gh.fn.name v.gh.fn.code) s fun s' =>
      GhOut s Ctx (St + BitVec.ofNat 64 yo) W SP (blocksAt s.mem P n) 256 s' ∧ KeepZ W z s.mem s'.mem :=
  wp_both ((GhFits.inst2560 v).ok L hyo h) (GZ L hyo h)

/-- What `KeepZ W (zw 512 a)` needs: the bytes from `a` on kept, those before
zero. -/
theorem KeepZ.of_zw {W : Addr} {a : Nat} {rs : List Region} {m m' : Mem} (ha : 512 ≤ a) (ha' : a ≤ 2560)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 a, 2560 - a⟩ : Region).Disjoint r)
    (hz : ∀ d, 512 ≤ d → d < a → m' (W + BitVec.ofNat 64 d) = 0) : KeepZ W (zw 512 a) m m' := fun d h₁ h₂ => by
  by_cases h : d < a
  · rw [show zw 512 a d = true by simp [zw]; omega, Scrub.ite_t rfl]; exact hz d h₁ h
  · rw [show zw 512 a d = false by simp [zw]; omega]
    exact hf _ fun r hr hc => hd r hr _ (by
      show ((W + BitVec.ofNat 64 d) - (W + BitVec.ofNat 64 a)).toNat + 1 ≤ 2560 - a
      rw [Offset.sub_toNat W (by omega) (by omega)]
      omega) hc

/-- `vg_ghash` that zeroes the 256 bytes of its working space and then clears
the registers before it returns. -/
theorem ghCallZ_wipeC (lv : VG.Impl.Scrub.X86_64.VecLevel) (v : GcmImpl) {c₀ : Prog isa}
    (hc : v.gh.fn.code = .seq (.seq c₀ (.block (wipeX .r8 0 256))) (.block (clrAfter lv)))
    (h8 : ∀ i ∈ instrs c₀, Taint.clobbers i .r8 = false) : GhCallZ v (zw 512 768) := by
  intro Ctx St W SP yo P n s L hyo h
  have hk := h.env.rsp
  obtain hcall := h.call L (by decide) hyo
  obtain ⟨t, u, e, q⟩ := gh_call v.gh hcall
  refine ⟨t, u, e, KeepZ.of_zw (by decide) (by decide) q.frame (fun r hr => ?_) fun d h₁ h₂ => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (L.st_w (by omega_using [hyo]) (.inr ⟨by decide, by decide⟩)).symm
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · rw [hk]; exact (L.stk_w (by decide)).symm
  · rw [hc] at e
    obtain hR : Covers [⟨s.gpr .r8, 256⟩] s.wr := fun a m ⟨r, hr, hcn⟩ => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hcall.writes a m ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by rw [← hcall.r8]; exact hcn⟩
    exact wipeR_zeroC lv (by decide) (Nat.le_refl _) (.inl rfl) h8 (by decide) e hR _ (by
      rw [h.r8]; rw [Offset.sub_toNat W h₁ (by omega)]; omega)

/-- `vg_ghash` that needs no working space: it leaves `W + 512` as it was. -/
theorem ghCallZ_free (v : GcmImpl) (gf : GhashFree v.gh.fn.code) : GhCallZ v zNo := by
  intro Ctx St W SP yo P n s L hyo h
  have hk := h.env.rsp
  obtain ⟨t, u, e, q⟩ := gh_callF v.gh gf (h.callF L hyo)
  refine ⟨t, u, e, KeepZ.of_frame q.frame fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (L.st_w (by omega_using [hyo]) (.inr ⟨by decide, by decide⟩)).symm
  · rw [hk]; exact (L.stk_w (by decide)).symm


/-- `ghash1_ok`, with what `GhCallZ` says. -/
theorem ghash1_okZ (v : GcmImpl) {z : Nat → Bool} (GZ : GhCallZ v z) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
    {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : Env Ctx St W SP s) (b : Reg) (o : Nat) (hb : b = .r14 ∨ b = .r15) {P : Addr}
    (hP : s.gpr b + BitVec.ofNat 64 o = P) (ho : o < 2 ^ 31)
    (hpy : (⟨St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hpw : (⟨P, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below SP 8).Disjoint ⟨P, 16⟩) (hpr : Covers [⟨P, 16⟩] (s.rd ++ s.wr)) :
    WP isa (ghash1 v.callees yo b o) s fun s' =>
      GhOut s Ctx (St + BitVec.ofNat 64 yo) W SP [blockAt s.mem P] 256 s' ∧ KeepZ W z s.mem s'.mem := by
  refine WP.seq (WP.mono (gh1Args_ok hyo he b o hb hP ho) fun s₁ a => ?_)
  have he₁ : Env Ctx St W SP s₁ := he.of_saved a.keep a.rd a.wr
  refine WP.mono (GZ.ok L hyo (P := P) (n := 1) ⟨he₁, a.rdi, a.rsi, a.rdx, a.rcx, a.r8, by decide,
    by simpa using hpy, by simpa using hpw, by simpa using hpk,
    by rw [a.rd, a.wr]; simpa using hpr⟩) fun s' ⟨h, k⟩ => ?_
  exact ⟨⟨h.rd.trans a.rd, h.wr.trans a.wr, fun r hr => (h.saved r hr).trans (a.keep r hr), a.mem ▸ h.frame,
    by rw [h.out, blocksAt_one, a.mem]⟩, a.mem ▸ k⟩

/-- Whether `absorb` calls `vg_ghash`, for `n` bytes after `r` buffered: if it
fills the buffer, or there are whole blocks after that. -/
def abZ (r n : Nat) : Bool :=
  decide (n ≠ 0 ∧ ((r ≠ 0 ∧ r + min (16 - r) n = 16) ∨ (n - crHead r n) / 16 ≠ 0))

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- `head_ok`, with what `GhCallZ` says. -/
theorem head_okZ {z : Nat → Bool} (GZ : GhCallZ v z) {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s : State}
    (h : AbsIn Ctx St W SP yo H x D n s) (hn : n ≠ 0) (ho : x.length % 16 ≠ 0) :
    WP isa (absorbHead v.callees yo) s fun s' =>
      AbsMid Ctx St W SP yo H x D n s.mem (min (16 - x.length % 16) n) s' ∧
      KeepZ W (zIf (decide (x.length % 16 + min (16 - x.length % 16) n = 16)) z) s.mem s'.mem := by
  obtain hlt : x.length % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn' := h.data.lt
  have he := h.env
  refine WP.seq (WP.mono (minLen_ok s h.rbx h.rbp (by omega_arith) hn') fun s₁ ⟨hcx, hg, hm, hrd, hwr⟩ => ?_)
  generalize hk : min (16 - x.length % 16) n = k at hcx ⊢
  obtain hk1 : 1 ≤ k := by omega_arith
  obtain hk16 : x.length % 16 + k ≤ 16 := by omega_arith
  obtain hkn : k ≤ n := by omega_arith
  obtain ⟨s₂, run₂, hdi, hsi, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rdi (.reg .r14),
      .alu .add .rdi (.reg .rbx), .alu .add .rdi (imm 32), .mov .rsi (.reg .r12)] s₁ = some s₂ ∧
      s₂.gpr .rdi = St + BitVec.ofNat 64 (32 + x.length % 16) ∧ s₂.gpr .rsi = D ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        hg _ (by decide : Reg.r14 ≠ .rcx), hg _ (by decide : Reg.rbx ≠ .rcx), he.r14, h.rbx,
        add_ofNat_assoc, Nat.add_comm]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hg _ (by decide : Reg.r12 ≠ .rcx), h.r12]
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  obtain lp : LoopPre s₂ D (St + BitVec.ofNat 64 (32 + x.length % 16)) k := by
    refine ⟨hsi, hdi, by rw [hg₂ _ (by decide) (by decide), hcx], hk1, by omega_arith, ?_, ?_, ?_⟩
    · rw [hrd₂, hwr₂, hrd, hwr]; exact (h.data.take hkn).rd
    · rw [hwr₂, hwr]; exact he.perm.stC (by omega_arith)
    · exact (h.data.take hkn).st.sub_right (Lay.stSub (by omega_arith))
  refine WP.seq (WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_)
  obtain hreg : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₃.gpr r = s.gpr r :=
    fun r a b c d e => by rw [hg₃ r a b, hg₂ r c d, hg r e]
  obtain h3rcx : s₃.gpr .rcx = BitVec.ofNat 64 k := by
    rw [hg₃ _ (by decide) (by decide), hg₂ _ (by decide) (by decide), hcx]
  rw [hm₂, hm] at hm₃
  rw [hrd₂, hrd] at hrd₃
  rw [hwr₂, hwr] at hwr₃
  -- The bytes copied, and the buffer.
  obtain hdk := length_bytesAt s.mem D k
  obtain hB : bytesAt s₃.mem (St + BitVec.ofNat 64 32) (x.length % 16 + k) =
      bytesAt s.mem (St + BitVec.ofNat 64 32) (x.length % 16) ++ bytesAt s.mem D k := by
    rw [hm₃, show St + BitVec.ofNat 64 (32 + x.length % 16) =
        St + BitVec.ofNat 64 32 + BitVec.ofNat 64 (x.length % 16) from (add_ofNat_assoc _ _ _).symm]
    have := bytesAt_writeBytes s.mem (St + BitVec.ofNat 64 32) (x.length % 16) (bytesAt s.mem D k)
      (by rw [hdk]; omega_arith)
    rwa [hdk] at this
  obtain fw : Frame [⟨St + BitVec.ofNat 64 (32 + x.length % 16), k⟩] s.mem s₃.mem := by
    rw [hm₃]; exact writeBytes_frame' _ hdk
  obtain hY : blockAt s₃.mem (St + BitVec.ofNat 64 yo) = blockAt s.mem (St + BitVec.ofNat 64 yo) :=
    blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain hH3 : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by omega_arith), h.hH]
  -- The block after the copy.
  obtain ⟨s₄, run₄, h12, hbp, hbx, hzf, hg₄, hm₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa
      [.alu .add .r12 (.reg .rcx), .alu .sub .rbp (.reg .rcx), .alu .add .rbx (.reg .rcx),
        .alu .cmp .rbx (imm 16)] s₃ = some s₄ ∧
      s₄.gpr .r12 = D + BitVec.ofNat 64 k ∧ s₄.gpr .rbp = BitVec.ofNat 64 (n - k) ∧
      s₄.gpr .rbx = BitVec.ofNat 64 (x.length % 16 + k) ∧
      s₄.zf = some (decide (x.length % 16 + k = 16)) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧
      s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    obtain e12 := hreg .r12 (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ebp := hreg .rbp (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ebx := hreg .rbx (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e12, h3rcx, h.r12]
    · simp [gpr_setReg, ebp, h3rcx, h.rbp, ofNat_sub hkn hn']
    · simp [gpr_setReg, ebx, h3rcx, h.rbx, ofNat_add_ofNat]
    · simp only [zf_arithFlags, ebx, h3rcx, h.rbx, ofNat_add_ofNat]
      rw [sub_beq (by omega_arith) (by decide)]
    · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  obtain he₄ : Env Ctx St W SP s₄ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [hg₄ _ (by decide) (by decide) (by decide),
        hreg _ (by decide) (by decide) (by decide) (by decide) (by decide)]) (hrd₄.trans hrd₃) (hwr₄.trans hwr₃)
  obtain hd₄ : DataOk St W SP s₄ D n := h.data.of_eq (hrd₄.trans hrd₃) (hwr₄.trans hwr₃)
  obtain kb : KeepZ W zNo s.mem s₄.mem := by
    rw [hm₄]
    exact KeepZ.of_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)).symm
  refine WP.ite (decide (x.length % 16 + k = 16)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · -- The buffer is full: absorbed.
    obtain h16 : x.length % 16 + k = 16 := by simpa using ht
    refine WP.mono (ghash1_okZ v GZ L hyo he₄ .r14 32 (.inl rfl) (P := St + BitVec.ofNat 64 32) (by rw [he₄.r14])
      (by decide) (L.st_st (.inl (by omega_arith)) (by omega_arith) (by decide)) (L.st_gh (GhFits.inst2560 v).fit (by decide))
      (L.stk_st (by decide)) (covers_left (he₄.perm.stC (by decide)))) fun s₅ ⟨g, kz⟩ => ?_
    refine ⟨⟨g.env he₄, hkn, by rw [g.saved _ (by decide)]; exact h12, by rw [g.saved _ (by decide)]; exact hbp,
      hd₄.of_eq g.rd g.wr, ?_, ?_, .inr (by omega_arith), ?_⟩, (kb.trans kz).congr fun d => by simp [zNo, zIf, h16]⟩
    · rw [blockAt_frame g.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega_arith)
        · exact L.ctx_gh (GhFits.inst2560 v).fit (by decide)
        · exact (L.stk_ctx (by decide)).symm, hm₄, hH3]
    · intro ha
      refine Proof.Gcm.absorb_complete ha (by rw [hdk]; exact h16) (B := bytesAt s₃.mem (St + BitVec.ofNat 64 32) 16) ?_ ?_
      · rw [← h16, hB, ha.2]
      · rw [g.out, hm₄, hY, hH3]; rfl
    · have f₁ : Frame (absFrame St W SP yo) s.mem s₃.mem := buf_absFrame (yo := yo) (W := W) (SP := SP) fw hk16
      obtain f₂ : Frame (absFrame St W SP yo) s₄.mem s₅.mem := gh_absFrame g.frame
      rw [← hm₄] at f₁; exact f₁.trans f₂
  · -- Not full: the data is used up.
    obtain h16 : x.length % 16 + k < 16 := by simp at hf; omega_arith
    obtain hkn' : k = n := by omega_arith
    refine WP.block_nil ⟨⟨he₄, hkn, h12, hbp, hd₄, by rw [hm₄]; exact hH3, fun ha => ?_, .inl (by omega_arith),
      by rw [hm₄]; exact buf_absFrame (yo := yo) (W := W) (SP := SP) fw hk16⟩,
      kb.congr fun d => by simp [zNo, zIf, show x.length % 16 + k ≠ 16 by omega_arith]⟩
    rw [hm₄]
    exact Proof.Gcm.absorb_fill ha (by rw [hdk]; exact h16) hY (by rw [hdk]; exact hB)

/-- `whole_ok`, with what `GhCallZ` says. -/
theorem whole_okZ {z : Nat → Bool} (GZ : GhCallZ v z) {H : Block} {x : List Byte} {D : Addr} {n : Nat} {m₀ : Mem}
    {j : Nat} {s : State} (h : AbsMid Ctx St W SP yo H x D n m₀ j s) (hm₀ : bytesAt s.mem D n = bytesAt m₀ D n) :
    WP isa (absorbWhole v.callees yo) s fun s' =>
      AbsMid Ctx St W SP yo H x D n m₀ (j + 16 * ((n - j) / 16)) s' ∧
      KeepZ W (zIf (!decide ((n - j) / 16 = 0)) z) s.mem s'.mem := by
  have hn' := h.data.lt
  have he := h.env
  obtain ⟨s₁, run₁, hdx, hcx, h12, hbp, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ := wholeSplit_ok .rdx .rcx (.inl ⟨rfl, rfl⟩) hn' h.le h.r12 h.rbp
  generalize hnb : (n - j) / 16 = nb at *
  obtain h16 : 16 * nb ≤ n - j := by omega_arith
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    hrd₁ hwr₁
  obtain hd₁ : DataOk St W SP s₁ D n := h.data.of_eq hrd₁ hwr₁
  refine WP.ite (decide (nb = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    simp only [Nat.mul_zero, Nat.add_zero]
    refine WP.block_nil ⟨⟨he₁, h.le, by rw [h12]; rfl, by rw [hbp]; rfl, hd₁, by rw [hm₁]; exact h.hH,
      fun ha => by rw [hm₁]; exact h.abs ha, h.whole, by rw [hm₁]; exact h.frame⟩,
      (KeepZ.of_eq hm₁).congr fun d => by simp [zNo, zIf]⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    obtain hw : (x.length + j) % 16 = 0 := h.whole.resolve_left (by omega_arith)
    obtain hdj := (h.data.drop h.le).take (k := 16 * nb) h16
    obtain h13 := he₁.r13; have h14 := he₁.r14; have h15 := he₁.r15
    obtain ⟨s₂, run₂, hdi, hsi, h8, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .r8 .r15 scrO) s₁ = some s₂ ∧
        s₂.gpr .rdi = Ctx + BitVec.ofNat 64 240 ∧ s₂.gpr .rsi = St + BitVec.ofNat 64 yo ∧
        s₂.gpr .r8 = W + BitVec.ofNat 64 512 ∧
        (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
        s₂.wr = s₁.wr := by
      refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h13]
      · simp [gpr_setReg, h14]
      · simp [gpr_setReg, h15]
      · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
      all_goals rfl
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    obtain he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
    refine WP.mono (GZ.ok L hyo (P := D + BitVec.ofNat 64 j) (n := nb) ⟨he₂, hdi, hsi,
      (by rw [hg₂ _ (by decide) (by decide) (by decide), hdx]),
      (by rw [hg₂ _ (by decide) (by decide) (by decide), hcx]), h8, (by have := hdj.lt; omega_arith),
      (hdj.st.sub_right (Lay.stSub (by omega_arith))).symm, Lay.gh_of_w (GhFits.inst2560 v).fit hdj.w, hdj.stk,
      (by rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact hdj.rd)⟩) fun s₃ ⟨g, kz⟩ => ?_
    obtain hg₃ : ∀ r, r ≠ .rdx → r ≠ .rcx → r ≠ .rax → r ≠ .r12 → r ≠ .rbp → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 →
        r ∈ calleeSaved → s₃.gpr r = s.gpr r := fun r a b c d e f g' i hr => by
      rw [g.saved r hr, hg₂ r f g' i, hg₁ r a b c d e]
    refine ⟨⟨g.env he₂, by omega_arith, ?_, ?_, hd₁.of_eq (g.rd.trans hrd₂) (g.wr.trans hwr₂), ?_, ?_,
      .inr (by omega_arith), ?_⟩, ?_⟩
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide), h12]
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide), hbp]
    · rw [blockAt_frame g.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega_arith)
        · exact L.ctx_gh (GhFits.inst2560 v).fit (by decide)
        · exact (L.stk_ctx (by decide)).symm), hm₂, hm₁]; exact h.hH
    · intro ha
      obtain ex : x ++ bytesAt m₀ D (j + 16 * nb) = (x ++ bytesAt m₀ D j) ++ bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * nb) := by
        rw [bytesAt_add, List.append_assoc]
      rw [ex]
      refine Proof.Gcm.absorb_whole (h.abs ha) (by simp [length_bytesAt]; omega_arith) (by simp [length_bytesAt]) ?_
      rw [g.out, hm₂, hm₁, h.hH, Proof.Gcm.blocksAt_eq]
      congr 2
      -- The data is as in `m₀`.
      obtain e₁ := congrArg (fun l => l.drop j) hm₀
      obtain e₂ : ∀ m : Mem, (bytesAt m D n).drop j = bytesAt m (D + BitVec.ofNat 64 j) (n - j) := fun m => by
        rw [show n = j + (n - j) by omega_arith, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
          Nat.add_sub_cancel_left]
      simp only [e₂] at e₁
      obtain e₃ := congrArg (fun l => l.take (16 * nb)) e₁
      obtain e₄ : ∀ m : Mem, (bytesAt m (D + BitVec.ofNat 64 j) (n - j)).take (16 * nb) =
          bytesAt m (D + BitVec.ofNat 64 j) (16 * nb) := fun m => by
        rw [show n - j = 16 * nb + (n - j - 16 * nb) by omega_arith, bytesAt_add,
          List.take_left' (length_bytesAt _ _ _)]
      simp only [e₄] at e₃
      exact e₃
    · have := g.frame; rw [hm₂, hm₁] at this; exact h.frame.trans (gh_absFrame this)
    · rw [hm₂, hm₁] at kz; exact kz.congr fun d => by simp [zIf, h0]

/-- `absorb_ok`, with what `GhCallZ` says: zero where `z` says if it called it (`abZ`). -/
theorem absorb_okZ {z : Nat → Bool} (GZ : GhCallZ v z) {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s : State}
    (h : AbsIn Ctx St W SP yo H x D n s) :
    WP isa (absorb v.callees yo) s fun s' =>
      AbsOut Ctx St W SP yo H x (x ++ bytesAt s.mem D n) s.mem s' ∧
      KeepZ W (zIf (abZ (x.length % 16) n) z) s.mem s'.mem := by
  have hn' := h.data.lt
  obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp h.rbp hn'
  obtain h₁ := h.keep hg₁ hm₁ hrd₁ hwr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨⟨h₁.env, fun ha => by rw [hm₁]; simpa [bytesAt] using ha, by rw [hm₁]; exact Frame.refl _ _⟩,
      (KeepZ.of_eq hm₁).congr fun d => by simp [zNo, zIf, abZ]⟩
  · have h0 : n ≠ 0 := by simpa using hf
    obtain hlt : x.length % 16 < 16 := Nat.mod_lt _ (by decide)
    obtain ⟨s₂, run₂, hzf₂, hg₂, hm₂, hrd₂, hwr₂⟩ := test_ok s₁ .rbx h₁.rbx (by omega_arith)
    obtain h₂ := h₁.keep hg₂ hm₂ hrd₂ hwr₂
    obtain hm₀ : s₂.mem = s.mem := hm₂.trans hm₁
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    refine WP.seq (WP.mono (Q := fun (s' : State) => AbsMid Ctx St W SP yo H x D n s.mem (crHead (x.length % 16) n) s' ∧
        KeepZ W (zIf (decide (x.length % 16 ≠ 0 ∧ x.length % 16 + min (16 - x.length % 16) n = 16)) z) s.mem s'.mem)
      (WP.ite (decide (x.length % 16 = 0)) (eval_e hzf₂) (fun ht => ?_) (fun hf => ?_)) fun s' hj => ?_)
    · have ho : x.length % 16 = 0 := by simpa using ht
      rw [show crHead (x.length % 16) n = 0 by simp [crHead, ho]]
      exact WP.block_nil ⟨⟨h₂.env, by omega_arith, by rw [h₂.r12]; simp, by rw [h₂.rbp, Nat.sub_zero], h₂.data, h₂.hH,
        fun ha => by rw [hm₀]; simpa [bytesAt] using ha, .inr (by omega_arith), by rw [← hm₀]; exact Frame.refl _ _⟩,
        (KeepZ.of_eq hm₀).congr fun d => by simp [zNo, zIf, ho]⟩
    · have ho : x.length % 16 ≠ 0 := by simpa using hf
      rw [show crHead (x.length % 16) n = min (16 - x.length % 16) n by simp [crHead, ho]]
      have := head_okZ v L hyo GZ h₂ h0 ho
      rw [hm₀] at this
      exact WP.mono this fun _ ⟨a, k⟩ => ⟨a, k.congr fun d => by simp [zIf, ho]⟩
    · obtain ⟨hj, k₁⟩ := hj
      refine WP.seq (WP.mono (whole_okZ v L hyo GZ hj (hj.data_eq hyo (.inr (by decide)))) fun s'' ⟨hj', k₂⟩ => ?_)
      generalize hJ : crHead (x.length % 16) n + 16 * ((n - crHead (x.length % 16) n) / 16) = J at hj'
      obtain hle := hj'.le
      obtain hJn : n - J < 16 := by have := hj.le; omega_arith
      obtain hw : n - J - 0 = 0 ∨ ((x ++ bytesAt s.mem D J).length + 0) % 16 = 0 := by
        rcases hj'.whole with e | e
        · exact .inl (by omega_arith)
        · exact .inr (by simp only [List.length_append, length_bytesAt, Nat.add_zero]; exact e)
      refine WP.mono (wp_both (tail_ok L hyo hj' hJn (hj'.data_eq hyo (.inr (by decide))))
        (tail_ok (gs := 0) L hyo (x := x ++ bytesAt s.mem D J) (D := D + BitVec.ofNat 64 J) (n := n - J) (j := 0)
          (m₀ := s''.mem) ⟨hj'.env, Nat.zero_le _, by rw [hj'.r12]; simp, by rw [hj'.rbp, Nat.sub_zero],
            hj'.data.drop hle, hj'.hH, fun ha => by simpa [bytesAt] using ha, hw, Frame.refl _ _⟩ (by omega_arith) rfl))
        fun s''' ⟨o, o'⟩ => ⟨o, ?_⟩
      obtain kt : KeepZ W zNo s''.mem s'''.mem := KeepZ.of_frame o'.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (L.st_w (by omega_using [hyo]) (.inr ⟨by decide, by decide⟩)).symm
        · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
        · exact Lay.disj_empty
        · exact (L.stk_w (by decide)).symm
      refine ((k₁.trans k₂).trans kt).congr fun d => ?_
      cases hz : z d
      · simp [zIf, zNo, hz]
      · simp only [zIf, zNo, abZ, hz, Bool.and_true, Bool.or_false]
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
        omega

/-- `absorbHead_out`, with what `GhCallZ` says. -/
theorem absorbHead_outZ {z : Nat → Bool} (GZ : GhCallZ v z) {H : Block} {x : List Byte} {D : Addr} {n : Nat}
    {s : State} (h : AbsIn Ctx St W SP yo H x D n s) (hn : n ≠ 0) (ho : x.length % 16 ≠ 0)
    (hle : n ≤ 16 - x.length % 16) :
    WP isa (absorbHead v.callees yo) s fun s' =>
      AbsOut Ctx St W SP yo H x (x ++ bytesAt s.mem D n) s.mem s' ∧
      KeepZ W (zIf (decide (x.length % 16 + n = 16)) z) s.mem s'.mem := by
  obtain e : min (16 - x.length % 16) n = n := Nat.min_eq_right hle
  refine WP.mono (head_okZ v L hyo GZ h hn ho) fun s' ⟨hm, k⟩ => ?_
  rw [e] at hm k
  exact ⟨⟨hm.env, hm.abs, hm.frame⟩, k⟩

end

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

theorem flushS_okZ {z : Nat → Bool} (GZ : GhCallZ v z) {H : Block} {x : List Byte} {s : State}
    (h : FlIn Ctx St W SP yo H x s) (hbx : s.gpr .rbx = BitVec.ofNat 64 (x.length % 16)) :
    WP isa (flushS v.callees yo) s fun s' =>
      FlOutS Ctx St W SP yo H x (x ++ zeros (padLen x.length)) s.mem s' ∧
      KeepZ W (zIf (decide (x.length % 16 ≠ 0)) z) s.mem s'.mem := by
  have he := h.env
  have hlt := Nat.mod_lt x.length (show 16 > 0 by decide)
  obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbx hbx (by omega_arith)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (x.length % 16 = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : x.length % 16 = 0 := by simpa using ht
    rw [Proof.Gcm.padLen_of_mod h0]
    exact WP.block_nil ⟨⟨he₁, by rw [hm₁]; exact h.hH, fun ha => by rw [hm₁]; simpa [zeros] using ha,
      by rw [hm₁]; exact Frame.refl _ _⟩, (KeepZ.of_eq hm₁).congr fun d => by simp [zNo, zIf, h0]⟩
  · have h0 : x.length % 16 ≠ 0 := by simpa using hf
    have h13 := he₁.r13; have h14 := he₁.r14; have h15 := he₁.r15
    obtain ⟨s₂, run₂, hm₂, hdi, hsi, hcx, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        ([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax] ++
          ptr .rdi .r14 64 ++ ptr .rsi .r14 32 ++ [.mov .rcx (.reg .rbx)]) s₁ = some s₂ ∧
        s₂.mem = (s.mem.writeW (St + BitVec.ofNat 64 64) (0 : BitVec 64)).writeW
          (St + BitVec.ofNat 64 64 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
        s₂.gpr .rdi = St + BitVec.ofNat 64 64 ∧ s₂.gpr .rsi = St + BitVec.ofNat 64 32 ∧
        s₂.gpr .rcx = BitVec.ofNat 64 (x.length % 16) ∧
        (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧
        s₂.wr = s.wr := by
      have w₁ := in_off he₁.perm.st (show 64 + 8 ≤ 80 by decide) (by decide)
      have w₂ := in_off he₁.perm.st (show 72 + 8 ≤ 80 by decide) (by decide)
      refine ⟨_, by xrun [h14, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [mem_setReg, add_ofNat_assoc, hm₁]; rfl
      · simp [gpr_setReg, h14]
      · simp [gpr_setReg, h14]
      · simp [gpr_setReg, hg₁, hbx]
      · intro r a b c d; simp [gpr_setReg, a, b, c, d, hg₁]
      · simp [rd_setReg, rd_arithFlags, hrd₁]
      · simp [wr_setReg, wr_arithFlags, hwr₁]
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide))
      hrd₂ hwr₂
    have lp : LoopPre s₂ (St + BitVec.ofNat 64 32) (St + BitVec.ofNat 64 64) (x.length % 16) :=
      ⟨hsi, hdi, hcx, by omega_arith, by omega_arith, covers_left (he₂.perm.stC (by omega_arith)),
        he₂.perm.stC (by omega_arith), L.st_st (.inl (by omega_arith)) (by omega_arith) (by omega_arith)⟩
    refine WP.seq (WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_)
    have he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
    -- The memory so far.
    have fz : Frame [⟨St + BitVec.ofNat 64 64, 16⟩] s.mem s₂.mem := by rw [hm₂]; exact zeroT_frame _ _
    have hB₂ : bytesAt s₂.mem (St + BitVec.ofNat 64 32) (x.length % 16) =
        bytesAt s.mem (St + BitVec.ofNat 64 32) (x.length % 16) :=
      bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by omega_arith)) (by omega_arith) (by decide))
        (by omega_arith)
    have hlen := length_bytesAt s₂.mem (St + BitVec.ofNat 64 32) (x.length % 16)
    have fc : Frame [⟨St + BitVec.ofNat 64 64, x.length % 16⟩] s₂.mem s₃.mem := by
      rw [hm₃]; exact writeBytes_frame' _ hlen
    have f₃ : Frame [⟨St + BitVec.ofNat 64 64, 16⟩] s.mem s₃.mem :=
      fz.trans (fc.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩)
    have hT : bytesAt s₃.mem (St + BitVec.ofNat 64 64) 16 =
        bytesAt s.mem (St + BitVec.ofNat 64 32) (x.length % 16) ++ zeros (16 - x.length % 16) := by
      rw [hm₃, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega_arith) (by decide), hlen, hB₂]
      refine congrArg (_ ++ ·) ?_
      have := zeroT_bytes s.mem (St + BitVec.ofNat 64 64)
      rw [← hm₂, show (16 : Nat) = x.length % 16 + (16 - x.length % 16) by omega_arith, bytesAt_add] at this
      have e := congrArg (List.drop (x.length % 16)) this
      rw [List.drop_left' (length_bytesAt _ _ _)] at e
      rw [e, show x.length % 16 + (16 - x.length % 16) = 16 by omega_arith, Spec.Gcm.zeros, List.drop_replicate]
      rfl
    have hY₃ : blockAt s₃.mem (St + BitVec.ofNat 64 yo) = blockAt s.mem (St + BitVec.ofNat 64 yo) :=
      blockAt_frame f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.st_st (.inl (by omega_using [hyo])) (by omega_using [hyo]) (by decide)
    have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
      rw [blockAt_frame f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide), h.hH]
    refine WP.mono (ghash1_okZ v GZ L hyo he₃ .r14 64 (.inl rfl) (P := St + BitVec.ofNat 64 64) (by rw [he₃.r14])
      (by decide) (L.st_st (.inl (by omega_using [hyo])) (by omega_using [hyo]) (by decide)) (L.st_gh (GhFits.inst2560 v).fit (by decide))
      (L.stk_st (by decide)) (covers_left (he₃.perm.stC (by decide)))) fun s₄ ⟨g, kz⟩ => ?_
    obtain kb : KeepZ W zNo s.mem s₃.mem := KeepZ.of_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
    refine ⟨⟨g.env he₃, ?_, ?_, ?_⟩, (kb.trans kz).congr fun d => by simp [zNo, zIf, h0]⟩
    · rw [blockAt_frame g.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega_arith)
        · exact L.ctx_gh (GhFits.inst2560 v).fit (by decide)
        · exact (L.stk_ctx (by decide)).symm), hH₃]
    · intro ha
      refine Proof.Gcm.absorb_pad ha h0 (B := bytesAt s₃.mem (St + BitVec.ofNat 64 64) 16) hT ?_
      rw [g.out, hY₃, hH₃]; rfl
    · refine (f₃.sub fun r hr => ?_).trans (gh_sFrame g.frame)
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩


end

/-! ## The pieces that keep `W + 448` -/

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block}
  {x₀ : List Byte} {P₀ : Nat} {t : Bool} {D : Addr} {n : Nat} {m₀ : Mem}

/-- `KeepZ`, with the 64 bytes at `W + 448` (the start of the whole blocks
function's `scratch`) as they were. -/
def KeepZ5 (W : Addr) (z : Nat → Bool) (m m' : Mem) : Prop :=
  (∀ x, (⟨W + BitVec.ofNat 64 448, 64⟩ : Region).Contains x 1 → m' x = m x) ∧ KeepZ W z m m'

theorem KeepZ5.of_eq {W : Addr} {m m' : Mem} (h : m' = m) : KeepZ5 W zNo m m' :=
  ⟨fun _ _ => by rw [h], KeepZ.of_eq h⟩

theorem KeepZ5.trans {W : Addr} {z₁ z₂ : Nat → Bool} {m₁ m₂ m₃ : Mem} (h₁ : KeepZ5 W z₁ m₁ m₂)
    (h₂ : KeepZ5 W z₂ m₂ m₃) : KeepZ5 W (fun d => z₁ d || z₂ d) m₁ m₃ :=
  ⟨fun x hx => (h₂.1 x hx).trans (h₁.1 x hx), h₁.2.trans h₂.2⟩

theorem KeepZ5.congr {W : Addr} {z z' : Nat → Bool} {m m' : Mem} (h : KeepZ5 W z m m') (e : ∀ d, z d = z' d) :
    KeepZ5 W z' m m' := ⟨h.1, h.2.congr e⟩

theorem KeepZ5.of_keep {W : Addr} {m m' : Mem} (h : Keep448 W m m') : KeepZ5 W zNo m m' :=
  ⟨fun x hx => h x (Region.sub_prefix (by decide) x hx), fun d a b => by
    show m' _ = m _
    exact h _ (by
      show (W + BitVec.ofNat 64 d - (W + BitVec.ofNat 64 448)).toNat + 1 ≤ 2112
      rw [Offset.sub_toNat W (by omega) (by omega)]; omega)⟩

theorem KeepZ5.of_frameZ {W : Addr} {z : Nat → Bool} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 448, 64⟩ : Region).Disjoint r) (hz : KeepZ W z m m') : KeepZ5 W z m m' :=
  ⟨fun _ hx => frame_at hf hd hx, hz⟩

/-- What `KeepZ5` says of the byte at `W + d`, from 448 on. -/
theorem KeepZ5.at {W : Addr} {z : Nat → Bool} {m m' : Mem} (h : KeepZ5 W z m m') {d : Nat} (h1 : 448 ≤ d)
    (h2 : d < 2560) : m' (W + BitVec.ofNat 64 d) = if 512 ≤ d ∧ z d = true then 0 else m (W + BitVec.ofNat 64 d) := by
  by_cases h5 : 512 ≤ d
  · rw [h.2 d h5 h2]
    by_cases hz : z d = true
    · rw [Scrub.ite_t hz, Scrub.ite_t ⟨h5, hz⟩]
    · rw [Scrub.ite_f hz, Scrub.ite_f (fun h => hz h.2)]
  · rw [h.1 _ (by
      show (W + BitVec.ofNat 64 d - (W + BitVec.ofNat 64 448)).toNat + 1 ≤ 64
      rw [Offset.sub_toNat W h1 (by omega)]; omega), Scrub.ite_f (fun h => h5 h.1)]

theorem k64_absFrame (L : Lay Ctx St W SP) :
    ∀ r ∈ absFrame St W SP 16, (⟨W + BitVec.ofNat 64 448, 64⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem k64_sFrame (L : Lay Ctx St W SP) :
    ∀ r ∈ sFrame St W SP 16, (⟨W + BitVec.ofNat 64 448, 64⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- `partWith_ok`'s pieces, keeping `W + 448`: so does `partWith`. -/
theorem partWith_keep (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool) {cr ab : Prog isa} {j k : Nat} {s : State}
    (hcr : ∀ {t : State}, CrIn Ctx St W SP R icb (P₀ + j) (D + BitVec.ofNat 64 j) k t →
      WP isa cr t fun t' => CrOut Ctx St W SP R icb (P₀ + j) (D + BitVec.ofNat 64 j) k t.mem t' ∧
        Keep448 W t.mem t'.mem)
    (hab : ∀ {x : List Byte} {t : State}, x.length % 16 = (P₀ + j) % 16 →
      AbsIn Ctx St W SP 16 H x (D + BitVec.ofNat 64 j) k t →
      WP isa ab t fun t' => AbsOut Ctx St W SP 16 H x (x ++ bytesAt t.mem (D + BitVec.ofNat 64 j) k) t.mem t' ∧
        Keep448 W t.mem t'.mem)
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s t)
    (hx : x₀.length % 16 = P₀ % 16) (hk : j + k ≤ n)
    (h12 : s.gpr .r12 = D + BitVec.ofNat 64 j) (hbp : s.gpr .rbp = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16))
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)) :
    WP isa (partWith enc cr ab) s fun s' => Keep448 W s.mem s'.mem := by
  have L := K.lay
  have hD := h.data
  have hj := h.le
  obtain hdj : DataW Ctx St W SP s (D + BitVec.ofNat 64 j) k := (hD.drop hj).take (by omega_arith)
  obtain hR := h.rounds K
  obtain hH := h.hH K
  obtain hxl : (x₀ ++ ctext enc (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j)).length % 16 = (P₀ + j) % 16 := by
    rw [List.length_append, length_ctext, length_bytesAt]; omega_arith
  cases enc
  · simp only [partWith, Bool.false_eq_true, ↓reduceIte]
    obtain hai : AbsIn Ctx St W SP 16 H (x₀ ++ ctext false (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j))
        (D + BitVec.ofNat 64 j) k s := ⟨h.env, h12, hbp, by rw [hbx, hxl], hdj.ok, hH⟩
    refine WP.seq (WP.mono (WP.with_rdwr (hab hxl hai)) fun s₂ ⟨⟨ao, k₂⟩, rd₂, wr₂⟩ => ?_)
    obtain sl₂ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      ao.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_absFrame L h₁ (by omega_arith))
        (by decide)
    obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := load_ok ao.env
      ((sl₂ 200 (by decide) (by decide)).trans hdat) ((sl₂ 208 (by decide) (by decide)).trans hlen)
      ((sl₂ 192 (by decide) (by decide)).trans htl)
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    obtain he₃ := ao.env.keep (load_env hg₃) hrd₃ hwr₃
    rw [toNat_mod16] at hbx₃
    obtain hR₃ : RoundsAt s₃.mem W R := hm₃ ▸ rounds_frame ao.frame (slot_absFrame L (by decide) (by decide)) hR
    obtain hdj₃ : DataW Ctx St W SP s₃ (D + BitVec.ofNat 64 j) k := hdj.of_eq (hrd₃.trans rd₂) (hwr₃.trans wr₂)
    exact WP.mono (hcr ⟨he₃, h12₃, hbp₃, hbx₃, hdj₃, hR₃⟩) fun s₄ ⟨_, k₄⟩ =>
      k₂.trans ((Keep448.of_eq hm₃).trans k₄)
  · simp only [partWith, ↓reduceIte]
    refine WP.seq (WP.mono (WP.with_rdwr (hcr ⟨h.env, h12, hbp, hbx, hdj, hR⟩))
      fun s₂ ⟨⟨co, k₂⟩, rd₂, wr₂⟩ => ?_)
    obtain sl₂ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      co.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_crFrame L hdj.ok h₁ (by omega_arith))
        (by decide)
    obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := load_ok co.env
      ((sl₂ 200 (by decide) (by decide)).trans hdat) ((sl₂ 208 (by decide) (by decide)).trans hlen)
      ((sl₂ 192 (by decide) (by decide)).trans htl)
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    obtain he₃ := co.env.keep (load_env hg₃) hrd₃ hwr₃
    rw [toNat_mod16] at hbx₃
    obtain hdj₃ : DataW Ctx St W SP s₃ (D + BitVec.ofNat 64 j) k := hdj.of_eq (hrd₃.trans rd₂) (hwr₃.trans wr₂)
    obtain hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
      rw [hm₃, blockAt_frame co.frame (fun r hr => (ctx_crFrame L hdj r hr).sub_left (Lay.ctxSub (by decide))), hH]
    obtain hai : AbsIn Ctx St W SP 16 H (x₀ ++ ctext true (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j))
        (D + BitVec.ofNat 64 j) k s₃ := ⟨he₃, h12₃, hbp₃, by rw [hbx₃, hxl], hdj₃.ok, hH₃⟩
    exact WP.mono (hab hxl hai) fun s₄ ⟨_, k₄⟩ => k₂.trans ((Keep448.of_eq hm₃).trans k₄)

/-- `partWith_keep`, with counter mode zeroing where `zc` says from `W + 512`,
and GHASH where `za` says. -/
theorem partWith_keepZ (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool) {cr ab : Prog isa} {j k : Nat} {s : State}
    {zc za : Nat → Bool}
    (hcr : ∀ {t : State}, CrIn Ctx St W SP R icb (P₀ + j) (D + BitVec.ofNat 64 j) k t →
      WP isa cr t fun t' => CrOut Ctx St W SP R icb (P₀ + j) (D + BitVec.ofNat 64 j) k t.mem t' ∧
        KeepZ5 W zc t.mem t'.mem)
    (hab : ∀ {x : List Byte} {t : State}, x.length % 16 = (P₀ + j) % 16 →
      AbsIn Ctx St W SP 16 H x (D + BitVec.ofNat 64 j) k t →
      WP isa ab t fun t' => AbsOut Ctx St W SP 16 H x (x ++ bytesAt t.mem (D + BitVec.ofNat 64 j) k) t.mem t' ∧
        KeepZ5 W za t.mem t'.mem)
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s t)
    (hx : x₀.length % 16 = P₀ % 16) (hk : j + k ≤ n)
    (h12 : s.gpr .r12 = D + BitVec.ofNat 64 j) (hbp : s.gpr .rbp = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16))
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)) :
    WP isa (partWith enc cr ab) s fun s' => KeepZ5 W (fun d => zc d || za d) s.mem s'.mem := by
  have L := K.lay
  have hD := h.data
  have hj := h.le
  obtain hdj : DataW Ctx St W SP s (D + BitVec.ofNat 64 j) k := (hD.drop hj).take (by omega_arith)
  obtain hR := h.rounds K
  obtain hH := h.hH K
  obtain hxl : (x₀ ++ ctext enc (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j)).length % 16 = (P₀ + j) % 16 := by
    rw [List.length_append, length_ctext, length_bytesAt]; omega_arith
  cases enc
  · simp only [partWith, Bool.false_eq_true, ↓reduceIte]
    obtain hai : AbsIn Ctx St W SP 16 H (x₀ ++ ctext false (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j))
        (D + BitVec.ofNat 64 j) k s := ⟨h.env, h12, hbp, by rw [hbx, hxl], hdj.ok, hH⟩
    refine WP.seq (WP.mono (WP.with_rdwr (hab hxl hai)) fun s₂ ⟨⟨ao, k₂⟩, rd₂, wr₂⟩ => ?_)
    obtain sl₂ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      ao.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_absFrame L h₁ (by omega_arith))
        (by decide)
    obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := load_ok ao.env
      ((sl₂ 200 (by decide) (by decide)).trans hdat) ((sl₂ 208 (by decide) (by decide)).trans hlen)
      ((sl₂ 192 (by decide) (by decide)).trans htl)
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    obtain he₃ := ao.env.keep (load_env hg₃) hrd₃ hwr₃
    rw [toNat_mod16] at hbx₃
    obtain hR₃ : RoundsAt s₃.mem W R := hm₃ ▸ rounds_frame ao.frame (slot_absFrame L (by decide) (by decide)) hR
    obtain hdj₃ : DataW Ctx St W SP s₃ (D + BitVec.ofNat 64 j) k := hdj.of_eq (hrd₃.trans rd₂) (hwr₃.trans wr₂)
    exact WP.mono (hcr ⟨he₃, h12₃, hbp₃, hbx₃, hdj₃, hR₃⟩) fun s₄ ⟨_, k₄⟩ =>
      ((k₂.trans (KeepZ5.of_eq hm₃)).trans k₄).congr fun d => by simp [zNo, Bool.or_comm]
  · simp only [partWith, ↓reduceIte]
    refine WP.seq (WP.mono (WP.with_rdwr (hcr ⟨h.env, h12, hbp, hbx, hdj, hR⟩))
      fun s₂ ⟨⟨co, k₂⟩, rd₂, wr₂⟩ => ?_)
    obtain sl₂ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      co.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_crFrame L hdj.ok h₁ (by omega_arith))
        (by decide)
    obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := load_ok co.env
      ((sl₂ 200 (by decide) (by decide)).trans hdat) ((sl₂ 208 (by decide) (by decide)).trans hlen)
      ((sl₂ 192 (by decide) (by decide)).trans htl)
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    obtain he₃ := co.env.keep (load_env hg₃) hrd₃ hwr₃
    rw [toNat_mod16] at hbx₃
    obtain hdj₃ : DataW Ctx St W SP s₃ (D + BitVec.ofNat 64 j) k := hdj.of_eq (hrd₃.trans rd₂) (hwr₃.trans wr₂)
    obtain hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
      rw [hm₃, blockAt_frame co.frame (fun r hr => (ctx_crFrame L hdj r hr).sub_left (Lay.ctxSub (by decide))), hH]
    obtain hai : AbsIn Ctx St W SP 16 H (x₀ ++ ctext true (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j))
        (D + BitVec.ofNat 64 j) k s₃ := ⟨he₃, h12₃, hbp₃, by rw [hbx₃, hxl], hdj₃.ok, hH₃⟩
    exact WP.mono (hab hxl hai) fun s₄ ⟨_, k₄⟩ => ((k₂.trans (KeepZ5.of_eq hm₃)).trans k₄).congr fun d => by simp [zNo]

/-- `part_ok`'s `partWith`, with callees that never touch their working
space: it keeps `W + 448`. -/
theorem part_keep (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee)
    (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool) {j k : Nat} {s : State}
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s t)
    (hx : x₀.length % 16 = P₀ % 16) (hk : j + k ≤ n)
    (h12 : s.gpr .r12 = D + BitVec.ofNat 64 j) (hbp : s.gpr .rbp = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16))
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)) :
    WP isa (partWith enc (crypt v.callees) (absorb v.callees 16)) s fun s' => Keep448 W s.mem s'.mem :=
  partWith_keep K enc
    (fun hc => WP.mono (crypt_okP v K.lay (CrCallP.free v cf) hc) fun _ ⟨o, f⟩ =>
      ⟨o, Keep448.of_frame f (k448_crFrameS K.lay hc.data.ok)⟩)
    (fun _ ha => WP.mono (absorb_ok v (G := GhFits.free v gf 2560) K.lay (.inr rfl) ha) fun _ o =>
      ⟨o.of0, Keep448.of_frame o.frame (k448_absFrame K.lay)⟩)
    h hx hk h12 hbp hbx hdat hlen htl

/-- `part_keep`, with an implementation of `vg_aes_ctr32` that leaves `W + 512`
as `C` says: zero where `z` says if it was called. -/
theorem part_keepZ {zg : Nat → Bool} (GZ : GhCallZ v zg) {sc : Nat} {z : Nat → Bool} (hsc : sc ≤ 2048) (C : CrCallZ v sc z)
    (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool) {j k : Nat} {s : State}
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s t)
    (hx : x₀.length % 16 = P₀ % 16) (hk : j + k ≤ n)
    (h12 : s.gpr .r12 = D + BitVec.ofNat 64 j) (hbp : s.gpr .rbp = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16))
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)) :
    WP isa (partWith enc (crypt v.callees) (absorb v.callees 16)) s fun s' =>
      KeepZ5 W (fun d => zIf (decide (crHead (P₀ + j) k < k)) z d || zIf (abZ ((P₀ + j) % 16) k) zg d) s.mem s'.mem :=
  partWith_keepZ K enc
    (fun hc => WP.mono (crypt_okZ v K.lay C hc) fun _ ⟨o, f, kz⟩ => ⟨o, fun x hx => frame_at f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hc.data.ok.w.sub_right (Lay.wSub (by decide))).symm
      · exact (K.lay.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact (K.lay.w_w (.inl (by decide)) (by decide) (by decide)).sub_right (Region.sub_prefix hsc)
      · exact (K.lay.stk_w (by decide)).symm) hx, kz⟩)
    (fun hxl ha => WP.mono (absorb_okZ v K.lay (.inr rfl) GZ ha) fun _ ⟨o, kz⟩ =>
      ⟨o, KeepZ5.of_frameZ o.frame (k64_absFrame K.lay) (by rw [hxl] at kz; exact kz)⟩)
    h hx hk h12 hbp hbx hdat hlen htl

/-- `headPart_ok`'s piece, with an implementation of `vg_ghash` that never
touches its working space: it keeps `W + 448`. -/
theorem headPart_keep (gf : GhashFree v.gh.fn.code) (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool) {s : State}
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ 0 s t)
    (hx : x₀.length % 16 = P₀ % 16) (hn : n ≠ 0)
    (h12 : s.gpr .r12 = D + BitVec.ofNat 64 0) (hbp : s.gpr .rbp = BitVec.ofNat 64 (headLen P₀ n))
    (hbx : s.gpr .rbx = BitVec.ofNat 64 ((P₀ + 0) % 16))
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 0)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (headLen P₀ n))
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + 0)) :
    WP isa (headPart v.callees enc) s fun s' => Keep448 W s.mem s'.mem := by
  obtain hlt := Nat.mod_lt (P₀ + 0) (show 16 > 0 by decide)
  obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbx hbx (by omega_arith)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain I₁ := h.regs (fun r _ => by rw [hg₁]) hm₁ hrd₁ hwr₁
  refine WP.ite (decide ((P₀ + 0) % 16 = 0)) (eval_e hz₁) (fun _ => ?_) (fun hf => ?_)
  · exact WP.block_nil (Keep448.of_eq hm₁)
  · have h0 : P₀ % 16 ≠ 0 := by simpa using hf
    obtain e : headLen P₀ n = min (16 - P₀ % 16) n := by simp [headLen, h0]
    obtain hk0 : headLen P₀ n ≠ 0 := by rw [e]; omega_arith
    obtain hle : headLen P₀ n ≤ 16 - (P₀ + 0) % 16 := by rw [e, Nat.add_zero]; omega_arith
    obtain hkn : 0 + headLen P₀ n ≤ n := by have := headLen_le P₀ n; omega_arith
    refine WP.mono (partWith_keep K enc
      (fun hc => WP.mono (cryptHead_okF hc hk0 (by rwa [Nat.add_zero])) fun s' ⟨hm, f⟩ => by
        obtain e' : min (16 - (P₀ + 0) % 16) (headLen P₀ n) = headLen P₀ n := Nat.min_eq_right hle
        rw [e'] at hm
        exact ⟨⟨hm.env, hm.rounds, hm.ctr, hm.done, hm.frame⟩, Keep448.of_frame f fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hc.data.ok.w.sub_right (Lay.wSub (by decide))).symm⟩)
      (fun hxl ha => WP.mono (absorbHead_out v (G := GhFits.free v gf 2560) K.lay (.inr rfl) ha hk0
          (by rw [hxl, Nat.add_zero]; exact h0) (by rw [hxl]; exact hle)) fun _ o =>
        ⟨o.of0, Keep448.of_frame o.frame (k448_absFrame K.lay)⟩)
      I₁ hx hkn (by rw [hg₁]; exact h12) (by rw [hg₁]; exact hbp) (by rw [hg₁]; exact hbx)
      (by rw [hm₁]; exact hdat) (by rw [hm₁]; exact hlen) (by rw [hm₁]; exact htl))
      fun s' k => (Keep448.of_eq hm₁).trans k

/-- `headPart_keep`, with what `GhCallZ` says: zero where `zg` says if it filled the block. -/
theorem headPart_keepZ {zg : Nat → Bool} (GZ : GhCallZ v zg) (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool) {s : State}
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ 0 s t)
    (hx : x₀.length % 16 = P₀ % 16) (hn : n ≠ 0)
    (h12 : s.gpr .r12 = D + BitVec.ofNat 64 0) (hbp : s.gpr .rbp = BitVec.ofNat 64 (headLen P₀ n))
    (hbx : s.gpr .rbx = BitVec.ofNat 64 ((P₀ + 0) % 16))
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 0)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (headLen P₀ n))
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + 0)) :
    WP isa (headPart v.callees enc) s fun s' =>
      KeepZ5 W (zIf (decide (P₀ % 16 ≠ 0 ∧ P₀ % 16 + headLen P₀ n = 16)) zg) s.mem s'.mem := by
  obtain hlt := Nat.mod_lt (P₀ + 0) (show 16 > 0 by decide)
  obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbx hbx (by omega_arith)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain I₁ := h.regs (fun r _ => by rw [hg₁]) hm₁ hrd₁ hwr₁
  refine WP.ite (decide ((P₀ + 0) % 16 = 0)) (eval_e hz₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : P₀ % 16 = 0 := by simpa using ht
    exact WP.block_nil ((KeepZ5.of_eq hm₁).congr fun d => by simp [zNo, zIf, h0])
  · have h0 : P₀ % 16 ≠ 0 := by simpa using hf
    obtain e : headLen P₀ n = min (16 - P₀ % 16) n := by simp [headLen, h0]
    obtain hk0 : headLen P₀ n ≠ 0 := by rw [e]; omega_arith
    obtain hle : headLen P₀ n ≤ 16 - (P₀ + 0) % 16 := by rw [e, Nat.add_zero]; omega_arith
    obtain hkn : 0 + headLen P₀ n ≤ n := by have := headLen_le P₀ n; omega_arith
    refine WP.mono (partWith_keepZ K enc (zc := zNo) (za := zIf (decide ((P₀ + 0) % 16 + headLen P₀ n = 16)) zg)
      (fun hc => WP.mono (cryptHead_okF hc hk0 (by rwa [Nat.add_zero])) fun s' ⟨hm, f⟩ => by
        obtain e' : min (16 - (P₀ + 0) % 16) (headLen P₀ n) = headLen P₀ n := Nat.min_eq_right hle
        rw [e'] at hm
        exact ⟨⟨hm.env, hm.rounds, hm.ctr, hm.done, hm.frame⟩, KeepZ5.of_keep (Keep448.of_frame f fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hc.data.ok.w.sub_right (Lay.wSub (by decide))).symm)⟩)
      (fun hxl ha => WP.mono (absorbHead_outZ v K.lay (.inr rfl) GZ ha hk0
          (by rw [hxl, Nat.add_zero]; exact h0) (by rw [hxl]; exact hle)) fun _ ⟨o, kz⟩ =>
        ⟨o, KeepZ5.of_frameZ o.frame (k64_absFrame K.lay) (by rw [hxl] at kz; exact kz)⟩)
      I₁ hx hkn (by rw [hg₁]; exact h12) (by rw [hg₁]; exact hbp) (by rw [hg₁]; exact hbx)
      (by rw [hm₁]; exact hdat) (by rw [hm₁]; exact hlen) (by rw [hm₁]; exact htl))
      fun s' k => ((KeepZ5.of_eq hm₁).trans k).congr fun d => by simp [zNo, zIf, h0]

end

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- `startS_ok`'s piece, with an implementation of `vg_ghash` that never
touches its working space: it keeps `W + 448`. -/
theorem startS_keep (gf : GhashFree v.gh.fn.code) {s : State} (he : Env Ctx St W SP s) {aL P : Nat}
    (hP : P < 2 ^ 64) (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P) :
    WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlushS v.callees) (.block []))) s fun s' => Keep448 W s.mem s'.mem := by
  obtain r₂ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rax (.mem (at_ .r15 tlenO)),
      .alu .test .rax (.reg .rax)] s = some s₂ ∧ s₂.zf = some (decide (P = 0)) ∧
      (∀ r, r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, r₂], ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, htl, and_self_beq hP]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  obtain he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
  refine WP.ite (decide (P = 0)) (eval_e hz₂) (fun _ => ?_) (fun _ => WP.block_nil (Keep448.of_eq hm₂))
  obtain r₃ := he₂.perm.wR (show 184 + 8 ≤ 2560 by decide)
  obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .alu .and .rbx (imm 15)] s₂ = some s₃ ∧ s₃.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧
      (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    obtain hand := and15 (BitVec.ofNat 64 aL)
    rw [imm_eq (by decide), toNat_mod16] at hand
    refine ⟨_, by xrun [he₂.r15, r₃], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hm₂, hal, hand]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  unfold firstFlushS
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  obtain he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  refine WP.mono (flushS_ok v (G := GhFits.free v gf 2560) L (yo := 16) (.inr rfl)
    (H := blockAt s₃.mem (Ctx + BitVec.ofNat 64 240)) (x := List.replicate aL 0) ⟨he₃, rfl⟩
    (by rw [hbx₃, List.length_replicate])) fun s₄ fo => ?_
  rw [← hm₂, ← hm₃]
  exact Keep448.of_frame fo.frame (k448_sFrame L)

/-- `startS_keep`, with what `GhCallZ` says: zero where `zg` says if it padded a partial block. -/
theorem startS_keepZ {zg : Nat → Bool} (GZ : GhCallZ v zg) {s : State} (he : Env Ctx St W SP s) {aL P : Nat}
    (hP : P < 2 ^ 64) (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P) :
    WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlushS v.callees) (.block []))) s fun s' =>
      KeepZ5 W (zIf (decide (P = 0 ∧ aL % 16 ≠ 0)) zg) s.mem s'.mem := by
  obtain r₂ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rax (.mem (at_ .r15 tlenO)),
      .alu .test .rax (.reg .rax)] s = some s₂ ∧ s₂.zf = some (decide (P = 0)) ∧
      (∀ r, r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, r₂], ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, htl, and_self_beq hP]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  obtain he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
  refine WP.ite (decide (P = 0)) (eval_e hz₂) (fun ht => ?_) (fun hf => WP.block_nil ((KeepZ5.of_eq hm₂).congr fun d => by
    simp only [decide_eq_false_iff_not] at hf; simp [zNo, zIf, hf]))
  obtain r₃ := he₂.perm.wR (show 184 + 8 ≤ 2560 by decide)
  obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .alu .and .rbx (imm 15)] s₂ = some s₃ ∧ s₃.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧
      (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    obtain hand := and15 (BitVec.ofNat 64 aL)
    rw [imm_eq (by decide), toNat_mod16] at hand
    refine ⟨_, by xrun [he₂.r15, r₃], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hm₂, hal, hand]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  unfold firstFlushS
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  obtain he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  have hP0 : P = 0 := by simpa using ht
  refine WP.mono (flushS_okZ v L (yo := 16) (.inr rfl) GZ
    (H := blockAt s₃.mem (Ctx + BitVec.ofNat 64 240)) (x := List.replicate aL 0) ⟨he₃, rfl⟩
    (by rw [hbx₃, List.length_replicate])) fun s₄ ⟨fo, kz⟩ => ?_
  rw [← hm₂, ← hm₃]
  exact KeepZ5.of_frameZ fo.frame (k64_sFrame L) (kz.congr fun d => by simp [zIf, List.length_replicate, hP0])

end

section
variable {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- `callBlocks_ok`'s call, of a function that leaves `Lb` in its `scratch`. -/
theorem callBlocks_okL (enc : Bool) {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
      Addr → Addr → Option (BitVec 8)} (hL : BlkLeft Lb (if enc then B.enc else B.dec).code M)
    {R : Nat} {D : Addr} {n q : Nat} {s : State} (h : ObIn M Ctx St W SP R D n q s) :
    WP isa (.frame (.push [.rax]) (.call (if enc then B.enc else B.dec).name
      (if enc then B.enc else B.dec).code) (.pop .rax 1)) s fun s₄ =>
      (∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r) ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      Frame (obFrame St W SP D q) s.mem s₄.mem ∧
      ∀ x, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 →
        s₄.mem x = (Lb Ctx (BitVec.ofNat 64 R) (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 16) D
          (BitVec.ofNat 64 q) (W + BitVec.ofNat 64 448) x).getD (s.mem x) := by
  cases enc
  · exact obFrameD_okL L B hL h
  · exact obFrameE_okL L B hL h

end

section
variable {M : Gcm.X86_64.Stitch.CtxMode} {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block}
  {x₀ : List Byte} {P₀ : Nat} {t : Bool} {D : Addr} {n : Nat} {m₀ : Mem}

/-- `blocks_ok`'s `streamBlocks`, of a function that leaves `Lb` in its
`scratch`: there, if there was a whole block, what `Lb` says. -/
theorem blocks_leaves (B : BlkFn M) (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb (if enc then B.enc else B.dec).code M) {j : Nat} {s : State}
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s t)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - j))
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)) :
    WP isa (streamBlocks (if enc then B.enc else B.dec)) s fun s' =>
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 = s.mem.readW (W + BitVec.ofNat 64 216) 64 ∧
      ∀ x, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 →
        s'.mem x = (if (n - j) / 16 = 0 then none else Lb Ctx (BitVec.ofNat 64 R) (St + BitVec.ofNat 64 48)
          (St + BitVec.ofNat 64 16) (D + BitVec.ofNat 64 j) (BitVec.ofNat 64 ((n - j) / 16))
          (W + BitVec.ofNat 64 448) x).getD (s.mem x) := by
  have L := K.lay
  have hD := h.data
  have hlt := hD.ok.lt
  have hj := h.le
  have he := h.env
  generalize hq : (n - j) / 16 = q
  unfold streamBlocks
  refine WP.seq (WP.mono (sb1_ok (L := n - j) (by omega_arith) he hlen) fun s₁ ⟨r₁, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  rw [hq] at r₁ z₁
  obtain he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  obtain h₁ : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s₁ t := h.regs (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) m₁ rd₁ wr₁
  refine WP.ite (decide (q = 0)) (by simp only [eval, z₁]) (fun hz => ?_) (fun hz => ?_)
  · simp only [decide_eq_true_eq] at hz
    subst hz
    exact WP.block_nil ⟨by rw [m₁], fun x _ => by rw [m₁]; rfl⟩
  · simp only [decide_eq_false_iff_not] at hz
    obtain hqk : j + q * 16 ≤ n := by omega_arith
    obtain hR₁ := h₁.rounds K
    refine WP.seq (WP.mono (ob2_ok (D := D + BitVec.ofNat 64 j) he₁ hR₁ (by rw [m₁]; exact hdat))
      fun s₂ ⟨a1, a2, a3, a4, a5, a6, a7, g₂, m₂, rd₂, wr₂⟩ => ?_)
    obtain he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)) rd₂ wr₂
    obtain m₂' : s₂.mem = s.mem := m₂.trans m₁
    obtain hdq : DataW Ctx St W SP s₂ (D + BitVec.ofNat 64 j) (n - j) := (hD.drop hj).of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)
    obtain obi : ObIn M Ctx St W SP R (D + BitVec.ofNat 64 j) (n - j) q s₂ := ⟨he₂, hdq, by omega_arith, K.t_c, K.t_w,
      K.t_d.sub_right (Offset.sub_base D (by omega_arith)), K.sp24, a1, a2, a3, a4, a5, by rw [a6, r₁], a7, K.rounds.2, K.t_s,
      (h.ext K).of_eq (rd₂.trans rd₁) (wr₂.trans wr₁) m₂'⟩
    refine WP.seq (WP.mono (callBlocks_okL B L enc hL obi) fun s₄ ⟨cs₄, rd₄, wr₄, fr₄, o₄⟩ => ?_)
    obtain he₄ : Env Ctx St W SP s₄ := he₂.of_saved cs₄ rd₄ wr₄
    obtain kp : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [fr₄.readW (Region.contains_self _ _) (slot_obFrame L hdq.ok.w (by omega_arith) K.t_w h₁ h₂) (by decide), m₂']
    refine WP.mono (sb3_ok (L := n - j) (by omega_arith) he₄ ((kp 200 (by decide) (by decide)).trans hdat)
      ((kp 208 (by decide) (by decide)).trans hlen) ((kp 192 (by decide) (by decide)).trans htl))
      fun s₅ ⟨_, _, _, _, f₅, _, _⟩ => ⟨?_, fun x hx => ?_⟩
    · rw [f₅.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide), kp 216 (by decide) (by decide)]
    · rw [frame_at f₅ (k448_slots L (by decide)) hx, o₄ x hx, m₂', ite_eq_right hz]

end

/-- Where `streamTextS` leaves the data kept, of `n` bytes after `P` of text:
at the start, if fewer than 256, else past the head and the whole blocks. -/
def stJ (P n : Nat) : Nat := if n < 256 then 0 else headLen P n + 16 * ((n - headLen P n) / 16)

theorem stJ_le (P n : Nat) : stJ P n ≤ n := by
  have := headLen_le P n
  unfold stJ; split <;> omega_arith

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block}
  {D : Addr} {n : Nat} {m₀ : Mem}

/-- `streamTextS enc`, with callees that never touch their working space and
a blocks function that leaves `Lb` in its `scratch`: the lengths and the data
kept at `192`–`216` past `stJ`, the whole length at `216` if it called the
blocks function, and in its `scratch` what `Lb` says if it did. -/
theorem streamTextS_leaves (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee)
    (B : BlkFn M) (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb (if enc then B.enc else B.dec).code M) {s : State}
    (he : Env Ctx St W SP s) (hm : s.mem = m₀) (hd : DataW Ctx St W SP s D n)
    (hcov : Covers [⟨Ctx, M.len⟩] (s.rd ++ s.wr)) (hbp : s.gpr .rbp = BitVec.ofNat 64 n)
    {a c₀ : List Byte} (hP : c₀.length < 2 ^ 64)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 a.length)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hyA : Hyp → Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀))
    (hyC : Hyp → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb c₀.length) :
    WP isa (streamTextS (v.withBlk B) enc) s fun s' =>
      s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (c₀.length + stJ c₀.length n) ∧
      s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (stJ c₀.length n) ∧
      s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - stJ c₀.length n) ∧
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 =
        (if n < 256 then s.mem.readW (W + BitVec.ofNat 64 216) 64 else BitVec.ofNat 64 n) ∧
      ∀ x, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 →
        s'.mem x = (if n < 256 then none else Lb Ctx (BitVec.ofNat 64 R) (St + BitVec.ofNat 64 48)
          (St + BitVec.ofNat 64 16) (D + BitVec.ofNat 64 (headLen c₀.length n))
          (BitVec.ofNat 64 ((n - headLen c₀.length n) / 16)) (W + BitVec.ofNat 64 448) x).getD (s.mem x) := by
  have hlt := hd.ok.lt
  have L := K.lay
  obtain hx : (a ++ zeros (padLen a.length) ++ c₀).length % 16 = c₀.length % 16 := by
    have := Proof.Gcm.length_pad_mod a.length
    simp only [List.length_append, Proof.Gcm.length_zeros]; omega_arith
  simp only [streamTextS]
  obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp hbp hlt
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ : Env Ctx St W SP s₁ := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (n = 0)) (eval_e hz₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    simp only [stJ, show (0 : Nat) < 256 by decide, ↓reduceIte, Nat.add_zero, Nat.sub_zero, BitVec.add_zero]
    exact WP.block_nil ⟨by rw [hm₁]; exact htl, by rw [hm₁]; exact hdat, by rw [hm₁]; exact hlen, by rw [hm₁],
      fun x _ => by rw [hm₁]; rfl⟩
  obtain h0 : n ≠ 0 := by simpa using hf
  obtain sl₁ : ∀ d, s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d => by
    rw [hm₁]
  refine WP.assoc (WP.seq (WP.mono (wp_both (startS_ok v K enc he₁ (hm₁.trans hm) (hd.of_eq hrd₁ hwr₁)
    (by rw [hrd₁, hwr₁]; exact hcov) (c₀ := c₀) hP (by rw [sl₁]; exact hal) (by rw [sl₁]; exact htl) hyA hyC)
    (startS_keep v L gf he₁ hP (by rw [sl₁]; exact hal) (by rw [sl₁]; exact htl)))
    fun s₂ ⟨⟨I₂, sl₂⟩, k₂⟩ => ?_))
  rw [hm₁] at k₂
  obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := load_ok I₂.env
    ((sl₂ 200 (by decide) (by decide)).trans ((sl₁ 200).trans hdat))
    ((sl₂ 208 (by decide) (by decide)).trans ((sl₁ 208).trans hlen))
    ((sl₂ 192 (by decide) (by decide)).trans ((sl₁ 192).trans htl))
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  rw [toNat_mod16] at hbx₃
  obtain I₃ := I₂.regs (load_env hg₃) hm₃ hrd₃ hwr₃
  obtain sl₃ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [hm₃, sl₂ d h₁ h₂, sl₁]
  obtain k₃ : Keep448 W s.mem s₃.mem := k₂.trans (Keep448.of_eq hm₃)
  obtain ⟨s₃', run₃', hcf, hg', hm', hrd', hwr'⟩ := small_ok s₃ hbp₃ hlt
  refine WP.seq (WP.of_runBlock ⟨s₃', run₃', ?_⟩)
  obtain I₃' := I₃.regs (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg' _ (by decide)) hm' hrd' hwr'
  obtain h12₃' : s₃'.gpr .r12 = D := by rw [hg' .r12 (by decide)]; exact h12₃
  obtain hbp₃' : s₃'.gpr .rbp = BitVec.ofNat 64 n := by rw [hg' .rbp (by decide)]; exact hbp₃
  obtain hbx₃' : s₃'.gpr .rbx = BitVec.ofNat 64 (c₀.length % 16) := by rw [hg' .rbx (by decide)]; exact hbx₃
  obtain sl₃' : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s₃'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [hm']; exact sl₃ d h₁ h₂
  obtain k₃' : Keep448 W s.mem s₃'.mem := k₃.trans (Keep448.of_eq hm')
  generalize hJ : stJ c₀.length n = J
  obtain hJn : J ≤ n := hJ ▸ stJ_le c₀.length n
  -- Where the rest starts: all of it if short, after the head and the whole blocks otherwise.
  refine WP.seq (WP.mono (Q := fun (s' : State) =>
      SInv M Hyp Ctx St W SP R H icb (a ++ zeros (padLen a.length) ++ c₀) c₀.length enc D n m₀ J s' false ∧
      s'.gpr .r12 = D + BitVec.ofNat 64 J ∧ s'.gpr .rbp = BitVec.ofNat 64 (n - J) ∧
      s'.gpr .rbx = BitVec.ofNat 64 ((c₀.length + J) % 16) ∧
      s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 J ∧
      s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - J) ∧
      s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (c₀.length + J) ∧
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 =
        (if n < 256 then s.mem.readW (W + BitVec.ofNat 64 216) 64 else BitVec.ofNat 64 n) ∧
      ∀ x, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 →
        s'.mem x = (if n < 256 then none else Lb Ctx (BitVec.ofNat 64 R) (St + BitVec.ofNat 64 48)
          (St + BitVec.ofNat 64 16) (D + BitVec.ofNat 64 (headLen c₀.length n))
          (BitVec.ofNat 64 ((n - headLen c₀.length n) / 16)) (W + BitVec.ofNat 64 448) x).getD (s.mem x))
    (WP.ite (decide (n < 256)) (eval_b hcf) (fun ht => ?_) (fun hf' => ?_))
    fun s' ⟨I, h12, hbp, hbx, hd', hl, ht, h216, hw⟩ => ?_)
  · obtain hn : n < 256 := by simpa using ht
    obtain hJ0 : J = 0 := by rw [← hJ]; simp [stJ, hn]
    subst hJ0
    refine WP.block_nil ⟨I₃', by simp [h12₃'], by rw [Nat.sub_zero]; exact hbp₃', by rw [hbx₃', Nat.add_zero],
      by rw [sl₃' 200 (by decide) (by decide), hdat]; simp, by rw [sl₃' 208 (by decide) (by decide), hlen, Nat.sub_zero],
      by rw [sl₃' 192 (by decide) (by decide), htl, Nat.add_zero], by rw [sl₃' 216 (by decide) (by decide)]; simp [hn],
      fun x hx => by rw [k₃' x hx]; simp [hn]⟩
  · obtain hn : ¬ n < 256 := by simpa using hf'
    -- The head.
    refine WP.seq (WP.mono (sHead_ok I₃'.env hlt hbx₃' hbp₃') fun s₄ ⟨hbp₄, hg₄, hl₄, ha₄, f₄, hrd₄, hwr₄⟩ => ?_)
    generalize hk : headLen c₀.length n = k at hbp₄ hl₄
    obtain hkn : k ≤ n := hk ▸ headLen_le c₀.length n
    obtain hk16 : k < 16 := by rw [← hk]; unfold headLen; split <;> omega_arith
    obtain hkw := headLen_whole c₀.length n
    rw [hk] at hkw
    obtain g₄ : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₄.gpr r = s₃'.gpr r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide)
    obtain I₄ := I₃'.slots K g₄ hrd₄ hwr₄ (by decide) (by decide) f₄
    obtain sl₄ : ∀ d, 176 ≤ d → d + 8 ≤ 208 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [f₄.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact K.lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)) (by decide), sl₃' d h₁ (by omega_arith)]
    obtain k₄ : Keep448 W s.mem s₄.mem := k₃'.trans (Keep448.of_frame f₄ (k448_slots L (by decide)))
    subst hk
    refine WP.seq (WP.mono (wp_both (headPart_ok v K enc I₄ hx h0 (by simp [hg₄ .r12 (by decide) (by decide), h12₃'])
      hbp₄ (by rw [hg₄ .rbx (by decide) (by decide), hbx₃', Nat.add_zero]) (by rw [sl₄ 200 (by decide) (by decide), hdat]; simp) hl₄
      (by rw [sl₄ 192 (by decide) (by decide), htl, Nat.add_zero]))
      (headPart_keep v gf K enc I₄ hx h0 (by simp [hg₄ .r12 (by decide) (by decide), h12₃'])
      hbp₄ (by rw [hg₄ .rbx (by decide) (by decide), hbx₃', Nat.add_zero]) (by rw [sl₄ 200 (by decide) (by decide), hdat]; simp) hl₄
      (by rw [sl₄ 192 (by decide) (by decide), htl, Nat.add_zero]))) fun s₅ ⟨⟨I₅, sl₅⟩, k₅⟩ => ?_)
    obtain k₅' : Keep448 W s.mem s₅.mem := k₄.trans k₅
    generalize hk : headLen c₀.length n = k at hkn hk16 hkw I₅ hl₄ hJ ⊢
    -- Past the head.
    refine WP.seq (WP.mono (next_ok I₅.env (D := D) (P := c₀.length) hkn hlt (by rw [sl₅ 208 (by decide) (by decide), hl₄])
      (by rw [sl₅ 200 (by decide) (by decide), sl₄ 200 (by decide) (by decide), hdat])
      (by rw [sl₅ 192 (by decide) (by decide), sl₄ 192 (by decide) (by decide), htl])
      (by rw [sl₅ 216 (by decide) (by decide), ha₄])) fun s₆ ⟨g₆, d₆, t₆, l₆, f₆, hrd₆, hwr₆⟩ => ?_)
    obtain I₆ := I₅.slots K (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide) (by decide)) hrd₆ hwr₆ (Nat.le_refl _) (by decide) f₆
    rw [Nat.zero_add] at I₆
    obtain k₆ : Keep448 W s.mem s₆.mem := k₅'.trans (Keep448.of_frame f₆ (k448_slots L (by decide)))
    obtain a₆ : s₆.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n := by
      rw [f₆.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide), sl₅ 216 (by decide) (by decide), ha₄]
    -- The whole blocks.
    refine WP.seq (WP.mono (wp_both (blocks_ok B K enc I₆ hx d₆ l₆ t₆ (fun hq => hkw.resolve_left (by omega_arith)))
      (blocks_leaves B K enc hL I₆ d₆ l₆ t₆)) fun s₇ ⟨⟨I₇, d₇, l₇, t₇⟩, a₇, c₇⟩ => ?_)
    obtain hq0 : ¬ (n - k) / 16 = 0 := by omega_using [hn, hkn, hk16]
    obtain hJ' : J = k + 16 * ((n - k) / 16) := by rw [← hJ]; simp [stJ, hn, hk]
    subst hJ'
    -- The rest.
    obtain ⟨s₈, run₈, h12₈, hbp₈, hbx₈, hg₈, hm₈, hrd₈, hwr₈⟩ := load_ok I₇.env d₇ l₇ t₇
    rw [toNat_mod16] at hbx₈
    obtain I₈ := I₇.regs (load_env hg₈) hm₈ hrd₈ hwr₈
    obtain e₈ : n - (k + 16 * ((n - k) / 16)) = (n - k) % 16 := by omega_arith
    exact WP.of_runBlock ⟨s₈, run₈, I₈, h12₈, by rw [hbp₈, e₈], hbx₈, by rw [hm₈]; exact d₇,
      by rw [hm₈, l₇, e₈], by rw [hm₈]; exact t₇, by rw [hm₈, a₇, a₆]; simp [hn],
      fun x hx => by rw [hm₈, c₇ x hx, ite_eq_right hq0, k₆ x hx]; simp [hn]⟩
  -- The rest.
  refine WP.mono (wp_both (part_ok v K enc I hx (j := J) (k := n - J) (by omega_arith) h12 hbp hbx hd' hl ht)
    (part_keep v gf cf K enc I hx (j := J) (k := n - J) (by omega_arith) h12 hbp hbx hd' hl ht))
    fun s'' ⟨⟨_, sl⟩, k''⟩ => ?_
  refine ⟨by rw [sl 192 (by decide) (by decide), ht], by rw [sl 200 (by decide) (by decide), hd'],
    by rw [sl 208 (by decide) (by decide), hl], by rw [sl 216 (by decide) (by decide), h216],
    fun x hx => by rw [k'' x hx, hw x hx]⟩

end

/-- Where the rest of `streamTextS`, of `n` bytes after `P` of text, leaves
zeros from `W + 512`: where `z` says if it called `vg_aes_ctr32`, and where
`zg` says if it called `vg_ghash`. -/
def zrest (z zg : Nat → Bool) (P n d : Nat) : Bool :=
  zIf (decide (crHead (P + stJ P n) (n - stJ P n) < n - stJ P n)) z d ||
    zIf (abZ ((P + stJ P n) % 16) (n - stJ P n)) zg d

/-- Where `streamTextS` leaves zeros from `W + 512` before the whole blocks,
where `zg` says: if it padded `aL` bytes of additional data, and if it
filled the partial block of the `P` bytes of text with the head. -/
def zpre (zg : Nat → Bool) (P aL n d : Nat) : Bool :=
  zIf (decide (n ≠ 0 ∧ P = 0 ∧ aL % 16 ≠ 0)) zg d ||
    zIf (decide (¬ n < 256 ∧ P % 16 ≠ 0 ∧ P % 16 + headLen P n = 16)) zg d

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block}
  {D : Addr} {n : Nat} {m₀ : Mem}

/-- `streamTextS_leaves`, with an implementation of `vg_aes_ctr32` that leaves
`W + 512` as `C` says (zero where `z` says if it was called), for the bytes
from 512 on: zero where `z` says if the rest called it. As there: the lengths and the data
kept at `192`–`216` past `stJ`, the whole length at `216` if it called the
blocks function, and in its `scratch` what `Lb` says if it did. -/
theorem streamTextS_leavesZ {zg : Nat → Bool} (GZ : GhCallZ v zg) {sc : Nat} {z : Nat → Bool} (hsc : sc ≤ 2048)
    (C : CrCallZ v sc z)
    (B : BlkFn M) (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb (if enc then B.enc else B.dec).code M) {s : State}
    (he : Env Ctx St W SP s) (hm : s.mem = m₀) (hd : DataW Ctx St W SP s D n)
    (hcov : Covers [⟨Ctx, M.len⟩] (s.rd ++ s.wr)) (hbp : s.gpr .rbp = BitVec.ofNat 64 n)
    {a c₀ : List Byte} (hP : c₀.length < 2 ^ 64)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 a.length)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hyA : Hyp → Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀))
    (hyC : Hyp → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb c₀.length) :
    WP isa (streamTextS (v.withBlk B) enc) s fun s' =>
      s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (c₀.length + stJ c₀.length n) ∧
      s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (stJ c₀.length n) ∧
      s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - stJ c₀.length n) ∧
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 =
        (if n < 256 then s.mem.readW (W + BitVec.ofNat 64 216) 64 else BitVec.ofNat 64 n) ∧
      ∀ d, 448 ≤ d → d < 2560 → s'.mem (W + BitVec.ofNat 64 d) =
        if 512 ≤ d ∧ zrest z zg c₀.length n d = true then 0
        else (if n < 256 then none else Lb Ctx (BitVec.ofNat 64 R) (St + BitVec.ofNat 64 48)
          (St + BitVec.ofNat 64 16) (D + BitVec.ofNat 64 (headLen c₀.length n))
          (BitVec.ofNat 64 ((n - headLen c₀.length n) / 16)) (W + BitVec.ofNat 64 448)
          (W + BitVec.ofNat 64 d)).getD
            (if 512 ≤ d ∧ zpre zg c₀.length a.length n d = true then 0 else s.mem (W + BitVec.ofNat 64 d)) := by
  have hlt := hd.ok.lt
  have L := K.lay
  obtain hx : (a ++ zeros (padLen a.length) ++ c₀).length % 16 = c₀.length % 16 := by
    have := Proof.Gcm.length_pad_mod a.length
    simp only [List.length_append, Proof.Gcm.length_zeros]; omega_arith
  simp only [streamTextS]
  obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp hbp hlt
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ : Env Ctx St W SP s₁ := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (n = 0)) (eval_e hz₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    simp only [stJ, show (0 : Nat) < 256 by decide, ↓reduceIte, Nat.add_zero, Nat.sub_zero, BitVec.add_zero]
    exact WP.block_nil ⟨by rw [hm₁]; exact htl, by rw [hm₁]; exact hdat, by rw [hm₁]; exact hlen, by rw [hm₁],
      fun d _ _ => by rw [hm₁]; simp [zrest, zpre, zIf, crHead, abZ, stJ]⟩
  obtain h0 : n ≠ 0 := by simpa using hf
  obtain sl₁ : ∀ d, s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d => by
    rw [hm₁]
  refine WP.assoc (WP.seq (WP.mono (wp_both (startS_ok v K enc he₁ (hm₁.trans hm) (hd.of_eq hrd₁ hwr₁)
    (by rw [hrd₁, hwr₁]; exact hcov) (c₀ := c₀) hP (by rw [sl₁]; exact hal) (by rw [sl₁]; exact htl) hyA hyC)
    (startS_keepZ v L GZ he₁ (aL := a.length) hP (by rw [sl₁]; exact hal) (by rw [sl₁]; exact htl)))
    fun s₂ ⟨⟨I₂, sl₂⟩, k₂⟩ => ?_))
  rw [hm₁] at k₂
  obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := load_ok I₂.env
    ((sl₂ 200 (by decide) (by decide)).trans ((sl₁ 200).trans hdat))
    ((sl₂ 208 (by decide) (by decide)).trans ((sl₁ 208).trans hlen))
    ((sl₂ 192 (by decide) (by decide)).trans ((sl₁ 192).trans htl))
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  rw [toNat_mod16] at hbx₃
  obtain I₃ := I₂.regs (load_env hg₃) hm₃ hrd₃ hwr₃
  obtain sl₃ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [hm₃, sl₂ d h₁ h₂, sl₁]
  obtain k₃ : KeepZ5 W (zIf (decide (c₀.length = 0 ∧ a.length % 16 ≠ 0)) zg) s.mem s₃.mem := (k₂.trans (KeepZ5.of_eq hm₃)).congr fun d => by simp only [zNo, Bool.or_false]
  obtain ⟨s₃', run₃', hcf, hg', hm', hrd', hwr'⟩ := small_ok s₃ hbp₃ hlt
  refine WP.seq (WP.of_runBlock ⟨s₃', run₃', ?_⟩)
  obtain I₃' := I₃.regs (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg' _ (by decide)) hm' hrd' hwr'
  obtain h12₃' : s₃'.gpr .r12 = D := by rw [hg' .r12 (by decide)]; exact h12₃
  obtain hbp₃' : s₃'.gpr .rbp = BitVec.ofNat 64 n := by rw [hg' .rbp (by decide)]; exact hbp₃
  obtain hbx₃' : s₃'.gpr .rbx = BitVec.ofNat 64 (c₀.length % 16) := by rw [hg' .rbx (by decide)]; exact hbx₃
  obtain sl₃' : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s₃'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [hm']; exact sl₃ d h₁ h₂
  obtain k₃' : KeepZ5 W (zIf (decide (c₀.length = 0 ∧ a.length % 16 ≠ 0)) zg) s.mem s₃'.mem := (k₃.trans (KeepZ5.of_eq hm')).congr fun d => by simp only [zNo, Bool.or_false]
  generalize hJ : stJ c₀.length n = J
  obtain hJn : J ≤ n := hJ ▸ stJ_le c₀.length n
  -- Where the rest starts: all of it if short, after the head and the whole blocks otherwise.
  refine WP.seq (WP.mono (Q := fun (s' : State) =>
      SInv M Hyp Ctx St W SP R H icb (a ++ zeros (padLen a.length) ++ c₀) c₀.length enc D n m₀ J s' false ∧
      s'.gpr .r12 = D + BitVec.ofNat 64 J ∧ s'.gpr .rbp = BitVec.ofNat 64 (n - J) ∧
      s'.gpr .rbx = BitVec.ofNat 64 ((c₀.length + J) % 16) ∧
      s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 J ∧
      s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - J) ∧
      s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (c₀.length + J) ∧
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 =
        (if n < 256 then s.mem.readW (W + BitVec.ofNat 64 216) 64 else BitVec.ofNat 64 n) ∧
      ∀ d, 448 ≤ d → d < 2560 → s'.mem (W + BitVec.ofNat 64 d) =
        (if n < 256 then none else Lb Ctx (BitVec.ofNat 64 R) (St + BitVec.ofNat 64 48)
          (St + BitVec.ofNat 64 16) (D + BitVec.ofNat 64 (headLen c₀.length n))
          (BitVec.ofNat 64 ((n - headLen c₀.length n) / 16)) (W + BitVec.ofNat 64 448) (W + BitVec.ofNat 64 d)).getD
            (if 512 ≤ d ∧ zpre zg c₀.length a.length n d = true then 0 else s.mem (W + BitVec.ofNat 64 d)))
    (WP.ite (decide (n < 256)) (eval_b hcf) (fun ht => ?_) (fun hf' => ?_))
    fun s' ⟨I, h12, hbp, hbx, hd', hl, ht, h216, hw⟩ => ?_)
  · obtain hn : n < 256 := by simpa using ht
    obtain hJ0 : J = 0 := by rw [← hJ]; simp [stJ, hn]
    subst hJ0
    refine WP.block_nil ⟨I₃', by simp [h12₃'], by rw [Nat.sub_zero]; exact hbp₃', by rw [hbx₃', Nat.add_zero],
      by rw [sl₃' 200 (by decide) (by decide), hdat]; simp, by rw [sl₃' 208 (by decide) (by decide), hlen, Nat.sub_zero],
      by rw [sl₃' 192 (by decide) (by decide), htl, Nat.add_zero], by rw [sl₃' 216 (by decide) (by decide)]; simp [hn],
      fun d h1 h2 => by rw [k₃'.at h1 h2]; simp [hn, zpre, zIf, h0]⟩
  · obtain hn : ¬ n < 256 := by simpa using hf'
    -- The head.
    refine WP.seq (WP.mono (sHead_ok I₃'.env hlt hbx₃' hbp₃') fun s₄ ⟨hbp₄, hg₄, hl₄, ha₄, f₄, hrd₄, hwr₄⟩ => ?_)
    generalize hk : headLen c₀.length n = k at hbp₄ hl₄
    obtain hkn : k ≤ n := hk ▸ headLen_le c₀.length n
    obtain hk16 : k < 16 := by rw [← hk]; unfold headLen; split <;> omega_arith
    obtain hkw := headLen_whole c₀.length n
    rw [hk] at hkw
    obtain g₄ : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₄.gpr r = s₃'.gpr r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide)
    obtain I₄ := I₃'.slots K g₄ hrd₄ hwr₄ (by decide) (by decide) f₄
    obtain sl₄ : ∀ d, 176 ≤ d → d + 8 ≤ 208 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [f₄.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact K.lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)) (by decide), sl₃' d h₁ (by omega_arith)]
    obtain k₄ : KeepZ5 W (zIf (decide (c₀.length = 0 ∧ a.length % 16 ≠ 0)) zg) s.mem s₄.mem := (k₃'.trans (KeepZ5.of_keep (Keep448.of_frame f₄ (k448_slots L (by decide))))).congr fun d => by
      simp only [zNo, Bool.or_false]
    subst hk
    refine WP.seq (WP.mono (wp_both (headPart_ok v K enc I₄ hx h0 (by simp [hg₄ .r12 (by decide) (by decide), h12₃'])
      hbp₄ (by rw [hg₄ .rbx (by decide) (by decide), hbx₃', Nat.add_zero]) (by rw [sl₄ 200 (by decide) (by decide), hdat]; simp) hl₄
      (by rw [sl₄ 192 (by decide) (by decide), htl, Nat.add_zero]))
      (headPart_keepZ v GZ K enc I₄ hx h0 (by simp [hg₄ .r12 (by decide) (by decide), h12₃'])
      hbp₄ (by rw [hg₄ .rbx (by decide) (by decide), hbx₃', Nat.add_zero]) (by rw [sl₄ 200 (by decide) (by decide), hdat]; simp) hl₄
      (by rw [sl₄ 192 (by decide) (by decide), htl, Nat.add_zero]))) fun s₅ ⟨⟨I₅, sl₅⟩, k₅⟩ => ?_)
    obtain k₅' := k₄.trans k₅
    generalize hk : headLen c₀.length n = k at hkn hk16 hkw I₅ hl₄ hJ ⊢
    -- Past the head.
    refine WP.seq (WP.mono (next_ok I₅.env (D := D) (P := c₀.length) hkn hlt (by rw [sl₅ 208 (by decide) (by decide), hl₄])
      (by rw [sl₅ 200 (by decide) (by decide), sl₄ 200 (by decide) (by decide), hdat])
      (by rw [sl₅ 192 (by decide) (by decide), sl₄ 192 (by decide) (by decide), htl])
      (by rw [sl₅ 216 (by decide) (by decide), ha₄])) fun s₆ ⟨g₆, d₆, t₆, l₆, f₆, hrd₆, hwr₆⟩ => ?_)
    obtain I₆ := I₅.slots K (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide) (by decide)) hrd₆ hwr₆ (Nat.le_refl _) (by decide) f₆
    rw [Nat.zero_add] at I₆
    obtain k₆ : KeepZ5 W (fun d => (zIf (decide (c₀.length = 0 ∧ a.length % 16 ≠ 0)) zg) d ||
        zIf (decide (c₀.length % 16 ≠ 0 ∧ c₀.length % 16 + headLen c₀.length n = 16)) zg d) s.mem s₆.mem :=
      (k₅'.trans (KeepZ5.of_keep (Keep448.of_frame f₆ (k448_slots L (by decide))))).congr fun d => by
      simp only [zNo, Bool.or_false]
    obtain a₆ : s₆.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n := by
      rw [f₆.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide), sl₅ 216 (by decide) (by decide), ha₄]
    -- The whole blocks.
    refine WP.seq (WP.mono (wp_both (blocks_ok B K enc I₆ hx d₆ l₆ t₆ (fun hq => hkw.resolve_left (by omega_arith)))
      (blocks_leaves B K enc hL I₆ d₆ l₆ t₆)) fun s₇ ⟨⟨I₇, d₇, l₇, t₇⟩, a₇, c₇⟩ => ?_)
    obtain hq0 : ¬ (n - k) / 16 = 0 := by omega_using [hn, hkn, hk16]
    obtain hJ' : J = k + 16 * ((n - k) / 16) := by rw [← hJ]; simp [stJ, hn, hk]
    subst hJ'
    -- The rest.
    obtain ⟨s₈, run₈, h12₈, hbp₈, hbx₈, hg₈, hm₈, hrd₈, hwr₈⟩ := load_ok I₇.env d₇ l₇ t₇
    rw [toNat_mod16] at hbx₈
    obtain I₈ := I₇.regs (load_env hg₈) hm₈ hrd₈ hwr₈
    obtain e₈ : n - (k + 16 * ((n - k) / 16)) = (n - k) % 16 := by omega_arith
    exact WP.of_runBlock ⟨s₈, run₈, I₈, h12₈, by rw [hbp₈, e₈], hbx₈, by rw [hm₈]; exact d₇,
      by rw [hm₈, l₇, e₈], by rw [hm₈]; exact t₇, by rw [hm₈, a₇, a₆]; simp [hn],
      fun d h1 h2 => by
        rw [hm₈, c₇ _ (show (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains (W + BitVec.ofNat 64 d) 1 by
          show (W + BitVec.ofNat 64 d - (W + BitVec.ofNat 64 448)).toNat + 1 ≤ 2112
          rw [Offset.sub_toNat W h1 (by omega)]; omega), ite_eq_right hq0, k₆.at h1 h2]
        simp [hn, zpre, zIf, h0, hk]⟩
  -- The rest.
  refine WP.mono (wp_both (part_ok v K enc I hx (j := J) (k := n - J) (by omega_arith) h12 hbp hbx hd' hl ht)
    (part_keepZ v GZ hsc C K enc I hx (j := J) (k := n - J) (by omega_arith) h12 hbp hbx hd' hl ht))
    fun s'' ⟨⟨_, sl⟩, k''⟩ => ?_
  refine ⟨by rw [sl 192 (by decide) (by decide), ht], by rw [sl 200 (by decide) (by decide), hd'],
    by rw [sl 208 (by decide) (by decide), hl], by rw [sl 216 (by decide) (by decide), h216],
    fun d h1 h2 => ?_⟩
  rw [k''.at h1 h2, hw d h1 h2]
  simp only [zrest, hJ]

end

/-! ## The functions -/

/-- The word `j` that `stream_encrypt` and `stream_decrypt` leave in `W` (`a 1`)
up to byte 224, of their argument registers `g` and stack arguments `a`, if
they write it: the saved registers (16 to 21), `rounds` (22), `aad_len`
(23), the text so far and the address and length of the data kept past
`stJ` (24 to 26), and the whole length if they called the blocks function
(27). -/
def streamWord (g : Reg → BitVec 64) (a : Nat → BitVec 64) (j : Nat) : Option (BitVec 64) :=
  match j with
  | 16 => some (g .rbx)
  | 17 => some (g .rbp)
  | 18 => some (g .r12)
  | 19 => some (g .r13)
  | 20 => some (g .r14)
  | 21 => some (g .r15)
  | 22 => some (g .rsi)
  | 23 => some (g .rcx)
  | 24 => some (BitVec.ofNat 64 ((g .r8).toNat + stJ (g .r8).toNat (a 0).toNat))
  | 25 => some (g .r9 + BitVec.ofNat 64 (stJ (g .r8).toNat (a 0).toNat))
  | 26 => some (BitVec.ofNat 64 ((a 0).toNat - stJ (g .r8).toNat (a 0).toNat))
  | 27 => if (a 0).toNat < 256 then none else some (BitVec.ofNat 64 (a 0).toNat)
  | _ => none

/-- What `stream_encrypt` and `stream_decrypt` leave at `x` in `W` (`a 1`), of
their argument registers `g` and stack arguments `a`, with a blocks function
that leaves `Lb` in its `scratch`: up to byte 224 the bytes of `streamWord`,
from 448 those `Lb` says if there were 256 bytes, and elsewhere nothing
written (`none`). -/
def streamL (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) (g : Reg → BitVec 64) (a : Nat → BitVec 64) (x : Addr) : Option (BitVec 8) :=
  if (x - a 1).toNat < 224 then
    (streamWord g a ((x - a 1).toNat / 8)).map fun w => w.extractLsb' (8 * ((x - a 1).toNat % 8)) 8
  else if (x - a 1).toNat < 448 ∨ (a 0).toNat < 256 then none
  else Lb (g .rdi) (BitVec.ofNat 64 (g .rsi).toNat) (g .rdx + BitVec.ofNat 64 48) (g .rdx + BitVec.ofNat 64 16)
    (g .r9 + BitVec.ofNat 64 (headLen (g .r8).toNat (a 0).toNat))
    (BitVec.ofNat 64 (((a 0).toNat - headLen (g .r8).toNat (a 0).toNat) / 16)) (a 1 + BitVec.ofNat 64 448) x

/-- `streamL`, from what is left: the words `streamWord` gives, the bytes
where it gives none and up to 448 as they were, and the blocks function's
`scratch`. -/
theorem streamL_of {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)} {g : Reg → BitVec 64} {a : Nat → BitVec 64} {m m' : Mem} {W : Addr} (hW : a 1 = W)
    (hw : ∀ j, 16 ≤ j → j < 28 → ∀ w, streamWord g a j = some w → m'.readW (W + BitVec.ofNat 64 (8 * j)) 64 = w)
    (hn : ∀ d, d < 2560 → (d < 224 → streamWord g a (d / 8) = none) →
      (224 ≤ d → d < 448 ∨ (a 0).toNat < 256) → m' (W + BitVec.ofNat 64 d) = m (W + BitVec.ofNat 64 d))
    (hb : ∀ d, 448 ≤ d → d < 2560 → ¬ (a 0).toNat < 256 →
      m' (W + BitVec.ofNat 64 d) = (Lb (g .rdi) (BitVec.ofNat 64 (g .rsi).toNat) (g .rdx + BitVec.ofNat 64 48)
        (g .rdx + BitVec.ofNat 64 16) (g .r9 + BitVec.ofNat 64 (headLen (g .r8).toNat (a 0).toNat))
        (BitVec.ofNat 64 (((a 0).toNat - headLen (g .r8).toNat (a 0).toNat) / 16)) (W + BitVec.ofNat 64 448)
        (W + BitVec.ofNat 64 d)).getD (m (W + BitVec.ofNat 64 d))) :
    ∀ x, (⟨W, 2560⟩ : Region).Contains x 1 → m' x = (streamL Lb g a x).getD (m x) := by
  intro x hx
  obtain hlt : (x - W).toNat < 2560 := by simp only [Region.Contains] at hx; omega_using [hx]
  generalize hd : (x - W).toNat = d at hlt
  obtain ex : x = W + BitVec.ofNat 64 d := by
    rw [← hd, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  subst ex
  simp only [streamL, hW, hd]
  by_cases h224 : d < 224
  · simp only [h224, ↓reduceIte]
    cases hj : streamWord g a (d / 8) with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      exact hn d hlt (fun _ => hj) fun h => absurd h (by omega_arith)
    | some w =>
      simp only [Option.map_some, Option.getD_some]
      obtain h16 : 16 ≤ d / 8 := by
        refine Nat.le_of_not_lt fun h => ?_
        rcases (by omega_arith : d / 8 = 0 ∨ d / 8 = 1 ∨ d / 8 = 2 ∨ d / 8 = 3 ∨ d / 8 = 4 ∨ d / 8 = 5 ∨ d / 8 = 6 ∨
          d / 8 = 7 ∨ d / 8 = 8 ∨ d / 8 = 9 ∨ d / 8 = 10 ∨ d / 8 = 11 ∨ d / 8 = 12 ∨ d / 8 = 13 ∨ d / 8 = 14 ∨
          d / 8 = 15) with e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e <;>
          rw [e] at hj <;> simp [streamWord] at hj
      rw [← Offset.add_add_eq W (show 8 * (d / 8) + d % 8 = d by omega_arith),
        byte_readW64' m' (W + BitVec.ofNat 64 (8 * (d / 8))) (j := d % 8) (by omega_arith),
        hw (d / 8) h16 (by omega_arith) w hj]
  · simp only [h224, ↓reduceIte]
    by_cases h448 : d < 448 ∨ (a 0).toNat < 256
    · simp only [h448, ↓reduceIte, Option.getD_none]
      exact hn d hlt (fun h' => absurd h' h224) fun _ => h448
    · simp only [h448, ↓reduceIte]
      rw [not_or] at h448
      exact hb d (by omega_arith) hlt h448.2


/-- Where `streamTextS` over a `vg_aes_ctr32` that zeroes where `z` says and a
`vg_ghash` that zeroes where `zg` says leaves zeros at `W + d` after the
whole blocks (`streamTextS_leavesZ`), of its argument registers `g` and stack
arguments `a`. -/
def zfin (z zg : Nat → Bool) (g : Reg → BitVec 64) (a : Nat → BitVec 64) (d : Nat) : Bool :=
  decide (512 ≤ d) && zrest z zg (g .r8).toNat (a 0).toNat d

/-- Where it leaves zeros at `W + d` before them (`zpre`). -/
def zpreF (zg : Nat → Bool) (g : Reg → BitVec 64) (a : Nat → BitVec 64) (d : Nat) : Bool :=
  decide (512 ≤ d) && zpre zg (g .r8).toNat (g .rcx).toNat (a 0).toNat d

theorem zpreF_lt {zg : Nat → Bool} {g : Reg → BitVec 64} {a : Nat → BitVec 64} {d : Nat} (h : d < 512) :
    zpreF zg g a d = false := by
  simp [zpreF, show ¬ 512 ≤ d by omega]

/-- `streamL`, with zeros where `zfin` says, and where it says nothing, where
`zpreF` says. -/
def streamLZ (z zg : Nat → Bool) (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
      Addr → Addr → Option (BitVec 8)) (g : Reg → BitVec 64) (a : Nat → BitVec 64) (x : Addr) : Option (BitVec 8) :=
  if (x - a 1).toNat < 2560 ∧ zfin z zg g a (x - a 1).toNat = true then some 0 else
    match streamL Lb g a x with
    | some b => some b
    | none => if (x - a 1).toNat < 2560 ∧ zpreF zg g a (x - a 1).toNat = true then some 0 else none

theorem off_W (W : Addr) {d : Nat} (hd : d < 2 ^ 64) : (W + BitVec.ofNat 64 d - W).toNat = d :=
  Mem.sub_ofNat_toNat W hd

/-- `streamL_of`, with the bytes where `zf` says zero. -/
theorem streamLZ_ofF {zf : Nat → Bool} (z512 : ∀ d, zf d = true → 512 ≤ d) {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
      Addr → Addr → Option (BitVec 8)} {g : Reg → BitVec 64} {a : Nat → BitVec 64} {m m' : Mem} {W : Addr}
    (hW : a 1 = W)
    (hz : ∀ d, d < 2560 → zf d = true → m' (W + BitVec.ofNat 64 d) = 0)
    (hw : ∀ j, 16 ≤ j → j < 28 → ∀ w, streamWord g a j = some w → m'.readW (W + BitVec.ofNat 64 (8 * j)) 64 = w)
    (hn : ∀ d, d < 2560 → zf d = false → (d < 224 → streamWord g a (d / 8) = none) →
      (224 ≤ d → d < 448 ∨ (a 0).toNat < 256) → m' (W + BitVec.ofNat 64 d) = m (W + BitVec.ofNat 64 d))
    (hb : ∀ d, 448 ≤ d → d < 2560 → zf d = false → ¬ (a 0).toNat < 256 →
      m' (W + BitVec.ofNat 64 d) = (Lb (g .rdi) (BitVec.ofNat 64 (g .rsi).toNat) (g .rdx + BitVec.ofNat 64 48)
        (g .rdx + BitVec.ofNat 64 16) (g .r9 + BitVec.ofNat 64 (headLen (g .r8).toNat (a 0).toNat))
        (BitVec.ofNat 64 (((a 0).toNat - headLen (g .r8).toNat (a 0).toNat) / 16)) (W + BitVec.ofNat 64 448)
        (W + BitVec.ofNat 64 d)).getD (m (W + BitVec.ofNat 64 d))) :
    ∀ x, (⟨W, 2560⟩ : Region).Contains x 1 →
      m' x = (if (x - a 1).toNat < 2560 ∧ zf (x - a 1).toNat = true then some 0 else streamL Lb g a x).getD (m x) := by
  let zone : Addr → Prop := fun y => (y - W).toNat < 2560 ∧ zf (y - W).toNat = true
  let m'' : Mem := fun y => if zone y then (streamL Lb g a y).getD (m y) else m' y
  have e₁ : ∀ d, d < 2560 → zf d = false → m'' (W + BitVec.ofNat 64 d) = m' (W + BitVec.ofNat 64 d) :=
    fun d hd hf => by
      show (if zone _ then _ else _) = _
      rw [Scrub.ite_f]; simp only [zone, off_W W (show d < 2 ^ 64 by omega), hf]; simp
  have e₂ : ∀ d, d < 2560 → zf d = true →
      m'' (W + BitVec.ofNat 64 d) = (streamL Lb g a (W + BitVec.ofNat 64 d)).getD (m (W + BitVec.ofNat 64 d)) :=
    fun d hd ht => by
      show (if zone _ then _ else _) = _
      rw [Scrub.ite_t]; simp only [zone, off_W W (show d < 2 ^ 64 by omega), ht]; exact ⟨hd, trivial⟩
  have sL : ∀ d, d < 2560 → 512 ≤ d → streamL Lb g a (W + BitVec.ofNat 64 d) =
      if (a 0).toNat < 256 then none else Lb (g .rdi) (BitVec.ofNat 64 (g .rsi).toNat) (g .rdx + BitVec.ofNat 64 48)
        (g .rdx + BitVec.ofNat 64 16) (g .r9 + BitVec.ofNat 64 (headLen (g .r8).toNat (a 0).toNat))
        (BitVec.ofNat 64 (((a 0).toNat - headLen (g .r8).toNat (a 0).toNat) / 16)) (W + BitVec.ofNat 64 448)
        (W + BitVec.ofNat 64 d) := fun d hd h5 => by
    simp only [streamL, hW, off_W W (show d < 2 ^ 64 by omega)]
    rw [Scrub.ite_f (by omega)]
    by_cases h : (a 0).toNat < 256
    · simp [h]
    · simp [h, show ¬ d < 448 by omega]
  have key := streamL_of (Lb := Lb) (g := g) (a := a) (m := m) (m' := m'') hW
    (fun j h₁ h₂ w hj => by
      have f : Frame [⟨W + BitVec.ofNat 64 512, 2048⟩] m' m'' := fun y hy => by
        show (if zone y then _ else _) = _
        rw [Scrub.ite_f]
        intro ⟨hl, hzz⟩
        apply hy _ (List.mem_singleton_self _)
        show (y - (W + BitVec.ofNat 64 512)).toNat + 1 ≤ 2048
        have h5 := z512 _ hzz
        have : y = W + BitVec.ofNat 64 (y - W).toNat := by
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
        rw [this, Offset.sub_toNat W h5 (by omega)]; omega
      rw [f.readW (r := ⟨W + BitVec.ofNat 64 (8 * j), 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by omega)) (by omega) (by omega)) (by decide)]
      exact hw j h₁ h₂ w hj)
    (fun d hd h1 h2 => by
      cases hzd : zf d
      · rw [e₁ d hd hzd]; exact hn d hd hzd h1 h2
      · rw [e₂ d hd hzd, sL d hd (z512 d hzd)]
        have h5 := z512 d hzd
        rcases h2 (by omega) with h | h
        · omega
        · simp [h])
    (fun d h4 hd h256 => by
      cases hzd : zf d
      · rw [e₁ d hd hzd]; exact hb d h4 hd hzd h256
      · rw [e₂ d hd hzd, sL d hd (z512 d hzd)]; simp [h256])
  intro x hx
  have hk := key x hx
  obtain hlt : (x - W).toNat < 2560 := by simp only [Region.Contains] at hx; omega
  simp only [hW]
  by_cases hzx : zf (x - W).toNat = true
  · rw [Scrub.ite_t ⟨hlt, hzx⟩]
    have : x = W + BitVec.ofNat 64 (x - W).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    rw [this]; exact hz _ hlt hzx
  · rw [Scrub.ite_f (fun h => hzx h.2)]
    rw [← hk]
    show m' x = if zone x then _ else m' x
    rw [Scrub.ite_f (fun h => hzx h.2)]

/-- `streamL_of` for `streamLZ`: the bytes where `zfin` says are zero, and the
others as `streamL_of` needs, with zeros where `zpreF` says in place of what
was there. -/
theorem streamLZ_of {z zg : Nat → Bool} {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
      Addr → Addr → Option (BitVec 8)} {g : Reg → BitVec 64} {a : Nat → BitVec 64} {m m' : Mem} {W : Addr}
    (hW : a 1 = W)
    (hz : ∀ d, d < 2560 → zfin z zg g a d = true → m' (W + BitVec.ofNat 64 d) = 0)
    (hw : ∀ j, 16 ≤ j → j < 28 → ∀ w, streamWord g a j = some w → m'.readW (W + BitVec.ofNat 64 (8 * j)) 64 = w)
    (hn : ∀ d, d < 2560 → zfin z zg g a d = false → (d < 224 → streamWord g a (d / 8) = none) →
      (224 ≤ d → d < 448 ∨ (a 0).toNat < 256) →
      m' (W + BitVec.ofNat 64 d) = if zpreF zg g a d = true then 0 else m (W + BitVec.ofNat 64 d))
    (hb : ∀ d, 448 ≤ d → d < 2560 → zfin z zg g a d = false → ¬ (a 0).toNat < 256 →
      m' (W + BitVec.ofNat 64 d) = (Lb (g .rdi) (BitVec.ofNat 64 (g .rsi).toNat) (g .rdx + BitVec.ofNat 64 48)
        (g .rdx + BitVec.ofNat 64 16) (g .r9 + BitVec.ofNat 64 (headLen (g .r8).toNat (a 0).toNat))
        (BitVec.ofNat 64 (((a 0).toNat - headLen (g .r8).toNat (a 0).toNat) / 16)) (W + BitVec.ofNat 64 448)
        (W + BitVec.ofNat 64 d)).getD (if zpreF zg g a d = true then 0 else m (W + BitVec.ofNat 64 d))) :
    ∀ x, (⟨W, 2560⟩ : Region).Contains x 1 → m' x = (streamLZ z zg Lb g a x).getD (m x) := by
  have z512 : ∀ d, zfin z zg g a d = true → 512 ≤ d := fun d h => by
    simp only [zfin, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
  let mP : Mem := fun y => if (y - W).toNat < 2560 ∧ zpreF zg g a (y - W).toNat = true then 0 else m y
  have eP : ∀ d, d < 2560 → mP (W + BitVec.ofNat 64 d) =
      if zpreF zg g a d = true then 0 else m (W + BitVec.ofNat 64 d) := fun d hd => by
    show (if _ then _ else _) = _
    simp only [off_W W (show d < 2 ^ 64 by omega), hd, true_and]
  have key := streamLZ_ofF (zf := zfin z zg g a) (m := mP) (m' := m') z512 hW hz hw
    (fun d hd hf h1 h2 => by rw [eP d hd]; exact hn d hd hf h1 h2)
    (fun d h4 hd hf h256 => by rw [eP d hd]; exact hb d h4 hd hf h256)
  intro x hx
  rw [key x hx]
  have hlt : (x - W).toNat < 2560 := by simp only [Region.Contains] at hx; omega
  simp only [streamLZ, hW]
  by_cases hzx : zfin z zg g a (x - W).toNat = true
  · rw [Scrub.ite_t ⟨hlt, hzx⟩, Scrub.ite_t ⟨hlt, hzx⟩]; rfl
  · rw [Scrub.ite_f (fun h => hzx h.2), Scrub.ite_f (fun h => hzx h.2)]
    cases streamL Lb g a x with
    | some b => rfl
    | none =>
      show (if _ then _ else _) = _
      by_cases hp : zpreF zg g a (x - W).toNat = true
      · rw [Scrub.ite_t ⟨hlt, hp⟩, Scrub.ite_t ⟨hlt, hp⟩]; rfl
      · rw [Scrub.ite_f (fun h => hp h.2), Scrub.ite_f (fun h => hp h.2)]; rfl

/-- What `stream_encrypt`'s precondition says of `St`, `W` and the stack
arguments, beyond `CryptCtx`. -/
theorem streamCryptPre_more {cl : Nat} {s : State} (hp : Proof.AesGcm.streamCryptPre cl s) :
    (⟨s.gpr .rdx, 80⟩ : Region).Disjoint ⟨stackArg s 1, 2560⟩ ∧
      (⟨s.gpr .rdx, 80⟩ : Region).Disjoint ⟨s.gpr .rsp + BitVec.ofNat 64 8, 16⟩ ∧
      (⟨s.gpr .r9, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨s.gpr .rsp + BitVec.ofNat 64 8, 16⟩ := by
  simp only [Proof.AesGcm.streamCryptPre, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.args,
    Proof.AesGcm.arg, Proof.AesGcm.rounds] at hp
  obtain ⟨-, -, -, -, -, -, d_sw, d_sa, -, d_da, -⟩ := hp
  obtain hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at d_sa d_da
  exact ⟨d_sw, d_sa, d_da⟩

open VG.Spec.Gcm (ctxH ctxCiph inc32) in
/-- One run of `stream_encrypt` (`enc`) or `stream_decrypt`, with callees that
never touch their working space and a blocks function that leaves `Lb` in
its `scratch`: it leaves `W` as `streamL` says, and its return address and
stack arguments as they were. -/
theorem streamS_leaves (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (enc : Bool)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb (if enc then B.enc else B.dec).code M) {s : State}
    (hp : Proof.AesGcm.streamCryptPre M.len s) (hok : M.ok s.mem (s.gpr .rdi)) :
    WP isa (.seq (.block cryptEntry) (.seq (streamTextS (v.withBlk B) enc) (.block restore))) s fun s' =>
      (∀ x, (⟨stackArg s 1, 2560⟩ : Region).Contains x 1 →
        s'.mem x = (streamL Lb s.gpr (fun i => stackArg s i) x).getD (s.mem x)) ∧
      ∀ x, (⟨s.gpr .rsp, 24⟩ : Region).Contains x 1 → s'.mem x = s.mem x := by
  have C := CryptCtx.of hp M.ge
  have X := CtxExt.ofCrypt hp hok
  have hR := C.rounds
  obtain ⟨dSW, dSA, dDA⟩ := streamCryptPre_more hp
  have hP : (s.gpr .r8).toNat < 2 ^ 64 := (s.gpr .r8).isLt
  generalize hc₀ : List.replicate (s.gpr .r8).toNat (0 : Byte) = c₀
  obtain hT : (s.gpr .r8).toNat = c₀.length := by rw [← hc₀, List.length_replicate]
  rw [hT] at hP
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rdx = St at *
  generalize hW : stackArg s 1 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hD : s.gpr .r9 = D at *
  generalize hn : (stackArg s 0).toNat = n at *
  have L := C.lay
  generalize hR' : (s.gpr .rsi).toNat = R at *
  refine WP.seq (WP.mono (cryptEntry_ok hCtx hSt hD hSP hW hn C.perm C.ww C.args C.dA (by rw [hR']; exact hR))
    fun s₁ E => ?_)
  have hRo : RoundsAt s₁.mem W R := hR' ▸ E.rounds
  have dCE : ∀ r ∈ [entryR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by decide))
  have K : SCtx M Ctx St W SP R (blockAt s₁.mem (Ctx + BitVec.ofNat 64 240)) D n s₁.mem := ⟨L, hRo, rfl, C.t_c,
    C.t_s, C.t_w, C.t_d, C.sp24, X.w, X.cs, X.cw, X.cd, X.ct, M.frame E.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact X.cw.sub_right (Lay.wSub (by decide))) X.w X.ok⟩
  have htl : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length := by
    rw [E.tlen, ← hT, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hal : s₁.mem.readW (W + BitVec.ofNat 64 184) 64 =
      BitVec.ofNat 64 (List.replicate (s.gpr .rcx).toNat (0 : Byte)).length := by
    rw [E.alen, List.length_replicate, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (wp_both
    (streamTextS_ok v B K enc (Hyp := False) (icb := 0) E.env rfl (C.data.of_eq E.rd E.wr)
      (by rw [E.rd, E.wr]; exact X.cov) E.rbp hP hal htl E.dat E.len (fun h => h.elim) (fun h => h.elim))
    (streamTextS_leaves v gf cf B K enc (Hyp := False) (icb := 0) hL E.env rfl (C.data.of_eq E.rd E.wr)
      (by rw [E.rd, E.wr]; exact X.cov) E.rbp hP hal htl E.dat E.len (fun h => h.elim) (fun h => h.elim)))
    fun s₂ ⟨⟨he₂, _, _, f₂, _⟩, l192, l200, l208, l216, lW⟩ => ?_)
  have hsv₂ : SavedAt s₂.mem W s := E.saved.frame f₂ (w_stFrame L C.data.ok.w C.t_w (by decide) (by decide))
  have hret : s₂.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₂ (ret_stFrame C.rS C.rD C.rW), ret_kept E.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide)))]
  refine WP.mono (exit_ok he₂.r15 (by rw [he₂.rsp, hSP]) (covers_left he₂.perm.w) hsv₂ (by rw [hSP, hret]))
    fun s' ⟨_, hm, _⟩ => ⟨?_, ?_⟩
  · -- `W`.
    have fE : ∀ d, d < 128 ∨ 216 ≤ d → d < 2560 → s₁.mem (W + BitVec.ofNat 64 d) = s.mem (W + BitVec.ofNat 64 d) := by
      intro d h₁ h₂
      refine frame_at E.frame (fun r hr => ?_) (Region.contains_self _ _)
      simp only [List.mem_singleton] at hr; subst hr
      rcases h₁ with h₁ | h₁
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
    have f2 : ∀ d, d < 192 ∨ (224 ≤ d ∧ d < 448) →
        s₂.mem (W + BitVec.ofNat 64 d) = s₁.mem (W + BitVec.ofNat 64 d) := by
      intro d h₁
      have hdl : d + 1 ≤ 2560 := by omega_arith
      refine frame_at f₂ (fun r hr => ?_) (Region.contains_self _ _)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ((dSW.sub_left (Lay.stSub (by decide))).sub_right (Lay.wSub hdl)).symm
      · exact (C.dE.sub_right (Lay.wSub hdl)).symm
      · simp only [tReg, Bool.false_eq_true, ↓reduceIte]; exact Lay.disj_empty
      · rcases h₁ with h₁ | h₁
        · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
        · exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact (C.t_w.sub_right (Lay.wSub hdl)).symm
    have rW : ∀ d, 128 ≤ d → d + 8 ≤ 192 →
        s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
        (w_stFrame L C.data.ok.w C.t_w h₁ h₂) (by decide)
    refine streamL_of (W := W) (m := s.mem) (m' := s'.mem) hW (fun j h₁ h₂ w hj => ?_) (fun d hd h224 h448 => ?_)
      (fun d h₁ hd hnot => ?_)
    · rw [hm]
      rcases (by omega_arith : j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
        j = 25 ∨ j = 26 ∨ j = 27) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.rbx, 128) (by simp [saved])
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.rbp, 136) (by simp [saved])
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.r12, 144) (by simp [saved])
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.r13, 152) (by simp [saved])
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.r14, 160) (by simp [saved])
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.r15, 168) (by simp [saved])
      · obtain rfl := Option.some.inj hj
        rw [show 8 * 22 = 176 from rfl, rW 176 (by decide) (by decide), hRo.1, ← hR', BitVec.ofNat_toNat,
          BitVec.setWidth_eq]
      · obtain rfl := Option.some.inj hj
        rw [show 8 * 23 = 184 from rfl, rW 184 (by decide) (by decide), E.alen]
      · simp only [streamWord, hT, hn] at hj
        obtain rfl := Option.some.inj hj; exact l192
      · simp only [streamWord, hT, hn, hD] at hj
        obtain rfl := Option.some.inj hj; exact l200
      · simp only [streamWord, hT, hn] at hj
        obtain rfl := Option.some.inj hj; exact l208
      · simp only [streamWord, hn] at hj
        by_cases h256 : n < 256
        · simp [h256] at hj
        · simp only [h256, ↓reduceIte, Option.some.injEq] at hj
          subst hj
          rw [show 8 * 27 = 216 from rfl, l216]; simp [h256]
    · rw [hm]
      by_cases h128 : d < 128
      · rw [f2 d (.inl (by omega_arith)), fE d (.inl h128) hd]
      by_cases h2 : d < 224
      · -- Only the whole length, if no blocks: as on entry.
        obtain hw := h224 h2
        obtain ⟨h27, h256⟩ : d / 8 = 27 ∧ n < 256 := by
          rcases (by omega_arith : d / 8 = 16 ∨ d / 8 = 17 ∨ d / 8 = 18 ∨ d / 8 = 19 ∨ d / 8 = 20 ∨ d / 8 = 21 ∨
            d / 8 = 22 ∨ d / 8 = 23 ∨ d / 8 = 24 ∨ d / 8 = 25 ∨ d / 8 = 26 ∨ d / 8 = 27) with
            e | e | e | e | e | e | e | e | e | e | e | e <;> rw [e] at hw <;> simp [streamWord, hn] at hw
          exact ⟨e, hw⟩
        obtain ed : W + BitVec.ofNat 64 d = W + BitVec.ofNat 64 216 + BitVec.ofNat 64 (d % 8) :=
          (Offset.add_add_eq W (show 216 + d % 8 = d by omega_arith)).symm
        rw [ed, byte_readW64' s₂.mem (W + BitVec.ofNat 64 216) (j := d % 8) (by omega_arith), l216]
        simp only [h256, ↓reduceIte]
        rw [← byte_readW64' s₁.mem (W + BitVec.ofNat 64 216) (j := d % 8) (by omega_arith), ← ed]
        exact fE d (.inr (by omega_arith)) hd
      · rcases h448 (by omega_arith) with h | h
        · rw [f2 d (.inr ⟨by omega_arith, h⟩), fE d (.inr (by omega_arith)) hd]
        · by_cases h4 : d < 448
          · rw [f2 d (.inr ⟨by omega_arith, h4⟩), fE d (.inr (by omega_arith)) hd]
          · rw [hn] at h
            rw [lW _ (Offset.contains _ (by omega_arith) (by omega_arith) (by decide))]
            simp only [h, ↓reduceIte, Option.getD_none]
            exact fE d (.inr (by omega_arith)) hd
    · rw [hn] at hnot
      rw [hm, lW _ (Offset.contains _ h₁ (by omega_arith) (by decide))]
      simp only [hnot, ↓reduceIte, hCtx, hR', hSt, hD, hT, hn]
      rw [fE d (.inr (by omega_arith)) hd]
  · -- The return address and the stack arguments.
    intro x hx
    rw [hm]
    have hsplit : (⟨SP, 8⟩ : Region).Contains x 1 ∨ (⟨SP + BitVec.ofNat 64 8, 16⟩ : Region).Contains x 1 := by
      by_cases h8 : (x - SP).toNat < 8
      · exact .inl (by simp only [Region.Contains] at hx ⊢; omega_using [h8])
      · refine .inr ?_
        have := (Offset.lt_iff x SP (d := 8) (n := 16) (by decide)).2
          ⟨by omega_arith, by simp only [Region.Contains] at hx; omega_using [hx]⟩
        simp only [Region.Contains]; omega_using [this]
    rcases hsplit with h | h
    · rw [frame_at f₂ (ret_stFrame C.rS C.rD C.rW) h, frame_at E.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide))) h]
    · refine (frame_at f₂ (fun r hr => ?_) h).trans (frame_at E.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact C.dA.sub_right (Lay.wSub (by decide))) h)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (dSA.sub_left (Lay.stSub (by decide))).symm
      · exact dDA.symm
      · simp only [tReg, Bool.false_eq_true, ↓reduceIte]; exact Lay.disj_empty
      · exact C.dA.sub_right (Lay.wSub (by decide))
      · exact C.dA.sub_right (Lay.wSub (by decide))
      · exact Offset.disjoint_below SP (n := 24) (d := 8) (k := 16) (by decide)


/-- One run of `stream_encrypt` (`enc`) or `stream_decrypt`, with callees that
never touch their working space and a blocks function that leaves `Lb` in
its `scratch`: it leaves `W` as `streamL` says, and its return address and
stack arguments as they were. -/
theorem streamS_leavesZ (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    {zg : Nat → Bool} (GZ : GhCallZ v zg) {sc : Nat} {z : Nat → Bool} (hsc : sc ≤ 2048) (CZ : CrCallZ v sc z) (enc : Bool)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb (if enc then B.enc else B.dec).code M) {s : State}
    (hp : Proof.AesGcm.streamCryptPre M.len s) (hok : M.ok s.mem (s.gpr .rdi)) :
    WP isa (.seq (.block cryptEntry) (.seq (streamTextS (v.withBlk B) enc) (.block restore))) s fun s' =>
      (∀ x, (⟨stackArg s 1, 2560⟩ : Region).Contains x 1 →
        s'.mem x = (streamLZ z zg Lb s.gpr (fun i => stackArg s i) x).getD (s.mem x)) ∧
      ∀ x, (⟨s.gpr .rsp, 24⟩ : Region).Contains x 1 → s'.mem x = s.mem x := by
  have C := CryptCtx.of hp M.ge
  have X := CtxExt.ofCrypt hp hok
  have hR := C.rounds
  obtain ⟨dSW, dSA, dDA⟩ := streamCryptPre_more hp
  have hP : (s.gpr .r8).toNat < 2 ^ 64 := (s.gpr .r8).isLt
  generalize hc₀ : List.replicate (s.gpr .r8).toNat (0 : Byte) = c₀
  obtain hT : (s.gpr .r8).toNat = c₀.length := by rw [← hc₀, List.length_replicate]
  rw [hT] at hP
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rdx = St at *
  generalize hW : stackArg s 1 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hD : s.gpr .r9 = D at *
  generalize hn : (stackArg s 0).toNat = n at *
  have L := C.lay
  generalize hR' : (s.gpr .rsi).toNat = R at *
  refine WP.seq (WP.mono (cryptEntry_ok hCtx hSt hD hSP hW hn C.perm C.ww C.args C.dA (by rw [hR']; exact hR))
    fun s₁ E => ?_)
  have hRo : RoundsAt s₁.mem W R := hR' ▸ E.rounds
  have dCE : ∀ r ∈ [entryR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by decide))
  have K : SCtx M Ctx St W SP R (blockAt s₁.mem (Ctx + BitVec.ofNat 64 240)) D n s₁.mem := ⟨L, hRo, rfl, C.t_c,
    C.t_s, C.t_w, C.t_d, C.sp24, X.w, X.cs, X.cw, X.cd, X.ct, M.frame E.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact X.cw.sub_right (Lay.wSub (by decide))) X.w X.ok⟩
  have htl : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length := by
    rw [E.tlen, ← hT, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hal : s₁.mem.readW (W + BitVec.ofNat 64 184) 64 =
      BitVec.ofNat 64 (List.replicate (s.gpr .rcx).toNat (0 : Byte)).length := by
    rw [E.alen, List.length_replicate, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (wp_both
    (streamTextS_ok v B K enc (Hyp := False) (icb := 0) E.env rfl (C.data.of_eq E.rd E.wr)
      (by rw [E.rd, E.wr]; exact X.cov) E.rbp hP hal htl E.dat E.len (fun h => h.elim) (fun h => h.elim))
    (streamTextS_leavesZ v GZ hsc CZ B K enc (Hyp := False) (icb := 0) hL E.env rfl (C.data.of_eq E.rd E.wr)
      (by rw [E.rd, E.wr]; exact X.cov) E.rbp hP hal htl E.dat E.len (fun h => h.elim) (fun h => h.elim)))
    fun s₂ ⟨⟨he₂, _, _, f₂, _⟩, l192, l200, l208, l216, lW⟩ => ?_)
  have hsv₂ : SavedAt s₂.mem W s := E.saved.frame f₂ (w_stFrame L C.data.ok.w C.t_w (by decide) (by decide))
  have hret : s₂.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₂ (ret_stFrame C.rS C.rD C.rW), ret_kept E.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide)))]
  refine WP.mono (exit_ok he₂.r15 (by rw [he₂.rsp, hSP]) (covers_left he₂.perm.w) hsv₂ (by rw [hSP, hret]))
    fun s' ⟨_, hm, _⟩ => ⟨?_, ?_⟩
  · -- `W`.
    have fE : ∀ d, d < 128 ∨ 216 ≤ d → d < 2560 → s₁.mem (W + BitVec.ofNat 64 d) = s.mem (W + BitVec.ofNat 64 d) := by
      intro d h₁ h₂
      refine frame_at E.frame (fun r hr => ?_) (Region.contains_self _ _)
      simp only [List.mem_singleton] at hr; subst hr
      rcases h₁ with h₁ | h₁
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
    have f2 : ∀ d, d < 192 ∨ (224 ≤ d ∧ d < 448) →
        s₂.mem (W + BitVec.ofNat 64 d) = s₁.mem (W + BitVec.ofNat 64 d) := by
      intro d h₁
      have hdl : d + 1 ≤ 2560 := by omega_arith
      refine frame_at f₂ (fun r hr => ?_) (Region.contains_self _ _)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ((dSW.sub_left (Lay.stSub (by decide))).sub_right (Lay.wSub hdl)).symm
      · exact (C.dE.sub_right (Lay.wSub hdl)).symm
      · simp only [tReg, Bool.false_eq_true, ↓reduceIte]; exact Lay.disj_empty
      · rcases h₁ with h₁ | h₁
        · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
        · exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact (C.t_w.sub_right (Lay.wSub hdl)).symm
    have rW : ∀ d, 128 ≤ d → d + 8 ≤ 192 →
        s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
        (w_stFrame L C.data.ok.w C.t_w h₁ h₂) (by decide)
    have zf : ∀ d, zfin z zg s.gpr (fun i => stackArg s i) d =
        (decide (512 ≤ d) && zrest z zg c₀.length n d) := fun d => by simp only [zfin, hT, hn]
    have zp : ∀ d, zpreF zg s.gpr (fun i => stackArg s i) d =
        (decide (512 ≤ d) && zpre zg c₀.length (List.replicate (s.gpr .rcx).toNat (0 : Byte)).length n d) :=
      fun d => by simp only [zpreF, hT, hn, List.length_replicate]
    refine streamLZ_of (z := z) (zg := zg) (W := W) (m := s.mem) (m' := s'.mem) hW (fun d hd hz => ?_)
      (fun j h₁ h₂ w hj => ?_) (fun d hd hzf h224 h448 => ?_) (fun d h₁ hd hzf hnot => ?_)
    · rw [zf, Bool.and_eq_true, decide_eq_true_eq] at hz
      rw [hm, lW d (by have := hz.1; omega) hd, Scrub.ite_t hz]
    · rw [hm]
      rcases (by omega_arith : j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
        j = 25 ∨ j = 26 ∨ j = 27) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.rbx, 128) (by simp [saved])
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.rbp, 136) (by simp [saved])
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.r12, 144) (by simp [saved])
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.r13, 152) (by simp [saved])
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.r14, 160) (by simp [saved])
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.r15, 168) (by simp [saved])
      · obtain rfl := Option.some.inj hj
        rw [show 8 * 22 = 176 from rfl, rW 176 (by decide) (by decide), hRo.1, ← hR', BitVec.ofNat_toNat,
          BitVec.setWidth_eq]
      · obtain rfl := Option.some.inj hj
        rw [show 8 * 23 = 184 from rfl, rW 184 (by decide) (by decide), E.alen]
      · simp only [streamWord, hT, hn] at hj
        obtain rfl := Option.some.inj hj; exact l192
      · simp only [streamWord, hT, hn, hD] at hj
        obtain rfl := Option.some.inj hj; exact l200
      · simp only [streamWord, hT, hn] at hj
        obtain rfl := Option.some.inj hj; exact l208
      · simp only [streamWord, hn] at hj
        by_cases h256 : n < 256
        · simp [h256] at hj
        · simp only [h256, ↓reduceIte, Option.some.injEq] at hj
          subst hj
          rw [show 8 * 27 = 216 from rfl, l216]; simp [h256]
    · rw [hm]
      by_cases hlo : ¬ d < 448
      · have h : n < 256 := by
          rcases h448 (by omega_arith) with h | h
          · omega_arith
          · rw [hn] at h; exact h
        rw [zf, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hzf
        rw [lW d (by omega_arith) hd, Scrub.ite_f (fun h' => by
          rcases hzf with hzf | hzf
          · exact hzf h'.1
          · rw [hzf] at h'; exact absurd h'.2 (by decide))]
        simp only [h, ↓reduceIte, Option.getD_none]
        rw [zp d, fE d (.inr (by omega_arith)) hd]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
      rw [zpreF_lt (by omega_arith)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases h128 : d < 128
      · rw [f2 d (.inl (by omega_arith)), fE d (.inl h128) hd]
      by_cases h2 : d < 224
      · -- Only the whole length, if no blocks: as on entry.
        obtain hw := h224 h2
        obtain ⟨h27, h256⟩ : d / 8 = 27 ∧ n < 256 := by
          rcases (by omega_arith : d / 8 = 16 ∨ d / 8 = 17 ∨ d / 8 = 18 ∨ d / 8 = 19 ∨ d / 8 = 20 ∨ d / 8 = 21 ∨
            d / 8 = 22 ∨ d / 8 = 23 ∨ d / 8 = 24 ∨ d / 8 = 25 ∨ d / 8 = 26 ∨ d / 8 = 27) with
            e | e | e | e | e | e | e | e | e | e | e | e <;> rw [e] at hw <;> simp [streamWord, hn] at hw
          exact ⟨e, hw⟩
        obtain ed : W + BitVec.ofNat 64 d = W + BitVec.ofNat 64 216 + BitVec.ofNat 64 (d % 8) :=
          (Offset.add_add_eq W (show 216 + d % 8 = d by omega_arith)).symm
        rw [ed, byte_readW64' s₂.mem (W + BitVec.ofNat 64 216) (j := d % 8) (by omega_arith), l216]
        simp only [h256, ↓reduceIte]
        rw [← byte_readW64' s₁.mem (W + BitVec.ofNat 64 216) (j := d % 8) (by omega_arith), ← ed]
        exact fE d (.inr (by omega_arith)) hd
      · rcases h448 (by omega_arith) with h | h
        · rw [f2 d (.inr ⟨by omega_arith, h⟩), fE d (.inr (by omega_arith)) hd]
        · rw [f2 d (.inr ⟨by omega_arith, by omega_arith⟩), fE d (.inr (by omega_arith)) hd]
    · rw [hn] at hnot
      rw [zf, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hzf
      rw [hm, lW d h₁ hd, Scrub.ite_f (fun h' => by
        rcases hzf with hzf | hzf
        · exact hzf h'.1
        · rw [hzf] at h'; exact absurd h'.2 (by decide))]
      simp only [hnot, ↓reduceIte, hCtx, hR', hSt, hD, hT, hn]
      rw [zp d, fE d (.inr (by omega_arith)) hd]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
  · -- The return address and the stack arguments.
    intro x hx
    rw [hm]
    have hsplit : (⟨SP, 8⟩ : Region).Contains x 1 ∨ (⟨SP + BitVec.ofNat 64 8, 16⟩ : Region).Contains x 1 := by
      by_cases h8 : (x - SP).toNat < 8
      · exact .inl (by simp only [Region.Contains] at hx ⊢; omega_using [h8])
      · refine .inr ?_
        have := (Offset.lt_iff x SP (d := 8) (n := 16) (by decide)).2
          ⟨by omega_arith, by simp only [Region.Contains] at hx; omega_using [hx]⟩
        simp only [Region.Contains]; omega_using [this]
    rcases hsplit with h | h
    · rw [frame_at f₂ (ret_stFrame C.rS C.rD C.rW) h, frame_at E.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide))) h]
    · refine (frame_at f₂ (fun r hr => ?_) h).trans (frame_at E.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact C.dA.sub_right (Lay.wSub (by decide))) h)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (dSA.sub_left (Lay.stSub (by decide))).symm
      · exact dDA.symm
      · simp only [tReg, Bool.false_eq_true, ↓reduceIte]; exact Lay.disj_empty
      · exact C.dA.sub_right (Lay.wSub (by decide))
      · exact C.dA.sub_right (Lay.wSub (by decide))
      · exact Offset.disjoint_below SP (n := 24) (d := 8) (k := 16) (by decide)


theorem streamWord_congr {g g' : Reg → BitVec 64} {a a' : Nat → BitVec 64}
    (hg : ∀ r, r ≠ .rax → r ≠ .rsp → g r = g' r) (ha : a 0 = a' 0) (j : Nat) :
    streamWord g a j = streamWord g' a' j := by
  simp only [streamWord, hg .rbx (by decide) (by decide), hg .rbp (by decide) (by decide),
    hg .r12 (by decide) (by decide), hg .r13 (by decide) (by decide), hg .r14 (by decide) (by decide),
    hg .r15 (by decide) (by decide), hg .rsi (by decide) (by decide), hg .rcx (by decide) (by decide),
    hg .r8 (by decide) (by decide), hg .r9 (by decide) (by decide), ha]

theorem streamL_congr (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) {g g' : Reg → BitVec 64} {a a' : Nat → BitVec 64}
    (hg : ∀ r, r ≠ .rax → r ≠ .rsp → g r = g' r) (ha₀ : a 0 = a' 0) (ha₁ : a 1 = a' 1) (x : Addr) :
    streamL Lb g a x = streamL Lb g' a' x := by
  simp only [streamL, streamWord_congr hg ha₀, ha₀, ha₁, hg .rdi (by decide) (by decide),
    hg .rsi (by decide) (by decide), hg .rdx (by decide) (by decide), hg .r8 (by decide) (by decide),
    hg .r9 (by decide) (by decide)]

theorem streamLZ_congr (z zg : Nat → Bool) (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
      Addr → Addr → Option (BitVec 8)) {g g' : Reg → BitVec 64} {a a' : Nat → BitVec 64}
    (hg : ∀ r, r ≠ .rax → r ≠ .rsp → g r = g' r) (ha₀ : a 0 = a' 0) (ha₁ : a 1 = a' 1) (x : Addr) :
    streamLZ z zg Lb g a x = streamLZ z zg Lb g' a' x := by
  unfold streamLZ zfin zpreF
  rw [ha₀, ha₁, hg .r8 (by decide) (by decide), hg .rcx (by decide) (by decide), streamL_congr Lb hg ha₀ ha₁ x]

/-- What the code of `stream_encrypt` or `stream_decrypt` leaves at `x` in its
frame of `withStackArgScratch 2584 1` from `s`, at `A = rsp - 2584`: its
first 8 bytes as they were, then the copies of the length and of `W`'s
address, `A + 24`, and in `W` what `streamL` says. -/
def streamFV (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) (s : State) (x : Addr) : Option (BitVec 8) :=
  if (x - (s.gpr .rsp - BitVec.ofNat 64 2584)).toNat < 8 then none
  else if (x - (s.gpr .rsp - BitVec.ofNat 64 2584)).toNat < 24 then
    some ((if (x - (s.gpr .rsp - BitVec.ofNat 64 2584)).toNat < 16 then stackArg s 0
      else s.gpr .rsp - BitVec.ofNat 64 2584 + BitVec.ofNat 64 24).extractLsb'
        (8 * ((x - (s.gpr .rsp - BitVec.ofNat 64 2584)).toNat % 8)) 8)
  else streamL Lb s.gpr (fun i => if i = 0 then stackArg s 0 else s.gpr .rsp - BitVec.ofNat 64 2584 + BitVec.ofNat 64 24) x

/-- What the code of `stream_encrypt` or `stream_decrypt` leaves at `x` in its
frame of `withStackArgScratch 2584 1` from `s`, at `A = rsp - 2584`: its
first 8 bytes as they were, then the copies of the length and of `W`'s
address, `A + 24`, and in `W` what `streamL` says. -/
def streamFVZ (z zg : Nat → Bool) (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) (s : State) (x : Addr) : Option (BitVec 8) :=
  if (x - (s.gpr .rsp - BitVec.ofNat 64 2584)).toNat < 8 then none
  else if (x - (s.gpr .rsp - BitVec.ofNat 64 2584)).toNat < 24 then
    some ((if (x - (s.gpr .rsp - BitVec.ofNat 64 2584)).toNat < 16 then stackArg s 0
      else s.gpr .rsp - BitVec.ofNat 64 2584 + BitVec.ofNat 64 24).extractLsb'
        (8 * ((x - (s.gpr .rsp - BitVec.ofNat 64 2584)).toNat % 8)) 8)
  else streamLZ z zg Lb s.gpr (fun i => if i = 0 then stackArg s 0 else s.gpr .rsp - BitVec.ofNat 64 2584 + BitVec.ofNat 64 24) x

theorem streamFV_congr (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) {s₁ s₂ : State} (hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r)
    (ha : stackArg s₁ 0 = stackArg s₂ 0) : streamFV Lb s₁ = streamFV Lb s₂ := by
  funext x
  have hsp := hg .rsp (by decide)
  have hL := streamL_congr Lb (g := s₁.gpr) (g' := s₂.gpr)
    (a := fun i => if i = 0 then stackArg s₂ 0 else s₂.gpr .rsp - BitVec.ofNat 64 2584 + BitVec.ofNat 64 24)
    (a' := fun i => if i = 0 then stackArg s₂ 0 else s₂.gpr .rsp - BitVec.ofNat 64 2584 + BitVec.ofNat 64 24)
    (fun r h _ => hg r h) rfl rfl x
  simp only [streamFV, hsp, ha, hL]

theorem streamFVZ_congr (z zg : Nat → Bool) (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
      Addr → Addr → Option (BitVec 8)) {s₁ s₂ : State} (hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r)
    (ha : stackArg s₁ 0 = stackArg s₂ 0) : streamFVZ z zg Lb s₁ = streamFVZ z zg Lb s₂ := by
  funext x
  have hsp := hg .rsp (by decide)
  have hL := streamLZ_congr z zg Lb (g := s₁.gpr) (g' := s₂.gpr)
    (a := fun i => if i = 0 then stackArg s₂ 0 else s₂.gpr .rsp - BitVec.ofNat 64 2584 + BitVec.ofNat 64 24)
    (a' := fun i => if i = 0 then stackArg s₂ 0 else s₂.gpr .rsp - BitVec.ofNat 64 2584 + BitVec.ofNat 64 24)
    (fun r h _ => hg r h) rfl rfl x
  simp only [streamFVZ, hsp, ha, hL]

open VG.Impl.StackScratch.X86_64 in
/-- The code of `stream_encrypt` or `stream_decrypt` (`c`, verified against the
contract with `scratch` that `withStackArgScratch 2584 1` gives it), which
leaves `W` as `streamL` says and its return address and stack arguments as
they were (`hl`), in that frame: what `streamFV` says. -/
theorem framedS_leaves {sig : Sig} {nm : String} {e : Elem} {n : Nat}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa} {P : State → Prop}
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hv : Verified X86_64.target c (Sig.scratchContract abi sig nm e n pre post wa 24 leak))
    (hP : ∀ s, (Sig.scratchContract abi sig nm e n pre post wa 24 leak).pre s → P s)
    (hl : ∀ s t s', P s → Exec isa c s t s' →
      (∀ x, (⟨stackArg s 1, 2560⟩ : Region).Contains x 1 →
        s'.mem x = (streamL Lb s.gpr (fun i => stackArg s i) x).getD (s.mem x)) ∧
      ∀ x, (⟨s.gpr .rsp, 24⟩ : Region).Contains x 1 → s'.mem x = s.mem x)
    (h1 : nStack sig = 1) (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 16 + 8 * nStack sig + n * e.size ≤ 2584)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ 24)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (24 + 2584) leak).pre s) {t : List Leak} {u : State}
    (he : Exec isa (withStackArgScratch 2584 (nStack sig) c) s t u) :
    ∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 2584, 2584⟩ : Region).Contains x 1 →
      u.mem x = (loseL (s.gpr .rsp - BitVec.ofNat 64 2584) 2584 (innerU c (narrowS sig e n 2584 s))
        (streamFV Lb s) x).getD (s.mem x) := by
  have hb' : 16 + 8 * nStack sig + n * e.size ≤ 2584 ∧ 2584 < 4096 ∧ 2584 % 8 = 0 := ⟨hb, by decide, by decide⟩
  have hW := framed_leaves (R := fun s => ⟨stackArg s 1, 2560⟩)
    (L := fun s x => streamL Lb s.gpr (fun i => stackArg s i) x) hv hP (fun s t s' hp he => (hl s t s' hp he).1)
    hk hb' (by decide) hsp hd hpre hs he
  have hH := framed_leaves (R := fun s => ⟨s.gpr .rsp, 24⟩) (L := fun _ _ => none) hv hP
    (fun s t s' hp he x hx => (hl s t s' hp he).2 x hx) hk hb' (by decide) hsp hd hpre hs he
  obtain ⟨hg, ha, hlst, hf⟩ := narrowS_args hk hb (by decide) hs
  obtain ⟨hrsp, -⟩ := narrowS_facts (nm := "") hk hb (by decide) hs
  rw [h1] at ha hlst hf
  generalize hA : s.gpr .rsp - BitVec.ofNat 64 2584 = A at hrsp hlst hf hW hH ⊢
  generalize hU : innerU c (narrowS sig e n 2584 s) = U at hW hH ⊢
  have hW' : stackArg (narrowS sig e n 2584 s) 1 = A + BitVec.ofNat 64 24 := hlst
  have ha0 : stackArg (narrowS sig e n 2584 s) 0 = stackArg s 0 := ha 0 (by decide)
  rw [hW'] at hW
  rw [hrsp] at hH
  intro x hx
  have hlt : (x - A).toNat < 2584 := by simp only [Region.Contains] at hx; omega_using [hx]
  generalize hdx : (x - A).toNat = d at hlt
  have ex : x = A + BitVec.ofNat 64 d := by
    rw [← hdx, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  subst ex
  have hxW' : d < 24 ∨ (⟨A + BitVec.ofNat 64 24, 2560⟩ : Region).Contains (A + BitVec.ofNat 64 d) 1 := by
    by_cases h : d < 24
    · exact .inl h
    · exact .inr (Offset.contains A (by omega_arith) (by omega_arith) (by decide))
  rcases loseL_cases A 2584 U (A + BitVec.ofNat 64 d) with hc | ⟨w, hc⟩
  rotate_left
  · rw [hc]
    rcases hxW' with h | h
    · rw [hH _ (Offset.contains_base A (by omega_arith) (by omega_arith)), hc]; rfl
    · rw [hW _ h, hc]; rfl
  rw [hc]
  unfold streamFV
  rw [hA]
  simp only [hdx]
  by_cases h8 : d < 8
  · simp only [h8, ↓reduceIte, Option.getD_none]
    rw [hH _ (Offset.contains_base A (by omega_arith) (by omega_arith)), hc]
    simp only [Option.getD_none]
    refine hf _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have := (Offset.lt_iff (A + BitVec.ofNat 64 d) A (d := 8) (n := 8 * (1 + 1)) (by decide)).1
      (by simp only [Region.Contains] at hc; rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl] at hc; omega_using [hc])
    rw [Mem.sub_ofNat_toNat A (show d < 2 ^ 64 by omega_arith)] at this
    omega_using [this, h8]
  · by_cases h24 : d < 24
    · simp only [h8, h24, ↓reduceIte, Option.getD_some]
      rw [hH _ (Offset.contains_base A (by omega_arith) (by omega_arith)), hc, Option.getD_none]
      have ex' : A + BitVec.ofNat 64 d = A + BitVec.ofNat 64 (8 * (d / 8)) + BitVec.ofNat 64 (d % 8) := by
        rw [Offset.add_add_eq _ (show 8 * (d / 8) + d % 8 = d by omega_arith)]
      rw [ex', byte_readW64' (narrowS sig e n 2584 s).mem (A + BitVec.ofNat 64 (8 * (d / 8))) (show d % 8 < 8 by omega_arith)]
      refine congrArg (BitVec.extractLsb' (8 * (d % 8)) 8) ?_
      by_cases h16 : d < 16
      · simp only [h16, ↓reduceIte]
        rw [← ha0, show 8 * (d / 8) = 8 * (0 + 1) by omega_arith]
        unfold stackArg stackArgAddr
        rw [hrsp]
      · simp only [h16, ↓reduceIte]
        rw [← hW', show 8 * (d / 8) = 8 * (1 + 1) by omega_arith]
        unfold stackArg stackArgAddr
        rw [hrsp]
    · simp only [h8, h24, ↓reduceIte]
      have hxW : (⟨A + BitVec.ofNat 64 24, 2560⟩ : Region).Contains (A + BitVec.ofNat 64 d) 1 :=
        Offset.contains A (by omega_arith) (by omega_arith) (by decide)
      rw [hW _ hxW, hc, streamL_congr Lb (g' := s.gpr) (a' := fun i => if i = 0 then stackArg s 0 else A + BitVec.ofNat 64 24)
        (fun r h₁ h₂ => hg r h₁ h₂) (by simp [ha0]) (by simp [hW'])]
      refine congrArg (Option.getD _) ?_
      refine hf _ fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      have := (Offset.lt_iff (A + BitVec.ofNat 64 d) A (d := 8) (n := 8 * (1 + 1)) (by decide)).1
        (by simp only [Region.Contains] at hc; rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl] at hc; omega_using [hc])
      rw [Mem.sub_ofNat_toNat A (show d < 2 ^ 64 by omega_arith)] at this
      omega_using [this, h24]

/-! ## Clearing the registers on the paths that call -/

open VG.Impl.Scrub.X86_64 (VecLevel)

open VG.Impl.StackScratch.X86_64 in
/-- The code of `stream_encrypt` or `stream_decrypt` (`c`, verified against the
contract with `scratch` that `withStackArgScratch 2584 1` gives it), which
leaves `W` as `streamL` says and its return address and stack arguments as
they were (`hl`), in that frame: what `streamFV` says. -/
theorem framedS_leavesZ {sig : Sig} {nm : String} {e : Elem} {n : Nat}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa} {P : State → Prop} {z zg : Nat → Bool}
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hv : Verified X86_64.target c (Sig.scratchContract abi sig nm e n pre post wa 24 leak))
    (hP : ∀ s, (Sig.scratchContract abi sig nm e n pre post wa 24 leak).pre s → P s)
    (hl : ∀ s t s', P s → Exec isa c s t s' →
      (∀ x, (⟨stackArg s 1, 2560⟩ : Region).Contains x 1 →
        s'.mem x = (streamLZ z zg Lb s.gpr (fun i => stackArg s i) x).getD (s.mem x)) ∧
      ∀ x, (⟨s.gpr .rsp, 24⟩ : Region).Contains x 1 → s'.mem x = s.mem x)
    (h1 : nStack sig = 1) (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 16 + 8 * nStack sig + n * e.size ≤ 2584)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ 24)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (24 + 2584) leak).pre s) {t : List Leak} {u : State}
    (he : Exec isa (withStackArgScratch 2584 (nStack sig) c) s t u) :
    ∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 2584, 2584⟩ : Region).Contains x 1 →
      u.mem x = (loseL (s.gpr .rsp - BitVec.ofNat 64 2584) 2584 (innerU c (narrowS sig e n 2584 s))
        (streamFVZ z zg Lb s) x).getD (s.mem x) := by
  have hb' : 16 + 8 * nStack sig + n * e.size ≤ 2584 ∧ 2584 < 4096 ∧ 2584 % 8 = 0 := ⟨hb, by decide, by decide⟩
  have hW := framed_leaves (R := fun s => ⟨stackArg s 1, 2560⟩)
    (L := fun s x => streamLZ z zg Lb s.gpr (fun i => stackArg s i) x) hv hP (fun s t s' hp he => (hl s t s' hp he).1)
    hk hb' (by decide) hsp hd hpre hs he
  have hH := framed_leaves (R := fun s => ⟨s.gpr .rsp, 24⟩) (L := fun _ _ => none) hv hP
    (fun s t s' hp he x hx => (hl s t s' hp he).2 x hx) hk hb' (by decide) hsp hd hpre hs he
  obtain ⟨hg, ha, hlst, hf⟩ := narrowS_args hk hb (by decide) hs
  obtain ⟨hrsp, -⟩ := narrowS_facts (nm := "") hk hb (by decide) hs
  rw [h1] at ha hlst hf
  generalize hA : s.gpr .rsp - BitVec.ofNat 64 2584 = A at hrsp hlst hf hW hH ⊢
  generalize hU : innerU c (narrowS sig e n 2584 s) = U at hW hH ⊢
  have hW' : stackArg (narrowS sig e n 2584 s) 1 = A + BitVec.ofNat 64 24 := hlst
  have ha0 : stackArg (narrowS sig e n 2584 s) 0 = stackArg s 0 := ha 0 (by decide)
  rw [hW'] at hW
  rw [hrsp] at hH
  intro x hx
  have hlt : (x - A).toNat < 2584 := by simp only [Region.Contains] at hx; omega_using [hx]
  generalize hdx : (x - A).toNat = d at hlt
  have ex : x = A + BitVec.ofNat 64 d := by
    rw [← hdx, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  subst ex
  have hxW' : d < 24 ∨ (⟨A + BitVec.ofNat 64 24, 2560⟩ : Region).Contains (A + BitVec.ofNat 64 d) 1 := by
    by_cases h : d < 24
    · exact .inl h
    · exact .inr (Offset.contains A (by omega_arith) (by omega_arith) (by decide))
  rcases loseL_cases A 2584 U (A + BitVec.ofNat 64 d) with hc | ⟨w, hc⟩
  rotate_left
  · rw [hc]
    rcases hxW' with h | h
    · rw [hH _ (Offset.contains_base A (by omega_arith) (by omega_arith)), hc]; rfl
    · rw [hW _ h, hc]; rfl
  rw [hc]
  unfold streamFVZ
  rw [hA]
  simp only [hdx]
  by_cases h8 : d < 8
  · simp only [h8, ↓reduceIte, Option.getD_none]
    rw [hH _ (Offset.contains_base A (by omega_arith) (by omega_arith)), hc]
    simp only [Option.getD_none]
    refine hf _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have := (Offset.lt_iff (A + BitVec.ofNat 64 d) A (d := 8) (n := 8 * (1 + 1)) (by decide)).1
      (by simp only [Region.Contains] at hc; rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl] at hc; omega_using [hc])
    rw [Mem.sub_ofNat_toNat A (show d < 2 ^ 64 by omega_arith)] at this
    omega_using [this, h8]
  · by_cases h24 : d < 24
    · simp only [h8, h24, ↓reduceIte, Option.getD_some]
      rw [hH _ (Offset.contains_base A (by omega_arith) (by omega_arith)), hc, Option.getD_none]
      have ex' : A + BitVec.ofNat 64 d = A + BitVec.ofNat 64 (8 * (d / 8)) + BitVec.ofNat 64 (d % 8) := by
        rw [Offset.add_add_eq _ (show 8 * (d / 8) + d % 8 = d by omega_arith)]
      rw [ex', byte_readW64' (narrowS sig e n 2584 s).mem (A + BitVec.ofNat 64 (8 * (d / 8))) (show d % 8 < 8 by omega_arith)]
      refine congrArg (BitVec.extractLsb' (8 * (d % 8)) 8) ?_
      by_cases h16 : d < 16
      · simp only [h16, ↓reduceIte]
        rw [← ha0, show 8 * (d / 8) = 8 * (0 + 1) by omega_arith]
        unfold stackArg stackArgAddr
        rw [hrsp]
      · simp only [h16, ↓reduceIte]
        rw [← hW', show 8 * (d / 8) = 8 * (1 + 1) by omega_arith]
        unfold stackArg stackArgAddr
        rw [hrsp]
    · simp only [h8, h24, ↓reduceIte]
      have hxW : (⟨A + BitVec.ofNat 64 24, 2560⟩ : Region).Contains (A + BitVec.ofNat 64 d) 1 :=
        Offset.contains A (by omega_arith) (by omega_arith) (by decide)
      rw [hW _ hxW, hc, streamLZ_congr z zg Lb (g' := s.gpr) (a' := fun i => if i = 0 then stackArg s 0 else A + BitVec.ofNat 64 24)
        (fun r h₁ h₂ => hg r h₁ h₂) (by simp [ha0]) (by simp [hW'])]
      refine congrArg (Option.getD _) ?_
      refine hf _ fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      have := (Offset.lt_iff (A + BitVec.ofNat 64 d) A (d := 8) (n := 8 * (1 + 1)) (by decide)).1
        (by simp only [Region.Contains] at hc; rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl] at hc; omega_using [hc])
      rw [Mem.sub_ofNat_toNat A (show d < 2 ^ 64 by omega_arith)] at this
      omega_using [this, h24]

/-! ## Clearing the registers on the paths that call -/

open VG.Impl.Scrub.X86_64 (VecLevel)

/-- A blocks function that leaves `Lb` in its `scratch` does, clearing the
registers before it returns. -/
theorem BlkLeft.wrapC (lv : VecLevel) {M : Gcm.X86_64.Stitch.CtxMode} {c : Prog isa}
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (h : BlkLeft Lb c M) : BlkLeft Lb (.seq c (.block (Impl.AesGcm.X86_64.clrAfter lv))) M := by
  intro s t s' hp he
  obtain ⟨u, e, rfl⟩ := exec_wrap_inv lv he
  exact h s t u hp e

section
variable (lv : VecLevel) (v : GcmImpl) (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee)
include gf cf

open VG.Impl.StackScratch.X86_64 (withStackArgScratch)
open Gcm.X86_64.Stitch (CtxMode)

/-- `vg_aes_gcm_stream_encrypt` clearing the registers after each call, with
callees that never touch their working space and a blocks function that
leaves `Lb` in its `scratch`: what it leaves in its frame (`streamFV`). -/
theorem streamEncryptClrB_leaves (B : BlkFn CtxMode.base)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb B.enc.code CtxMode.base) {s : State}
    (hs : (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608).pre s) {t : List Leak} {u : State}
    (he : Exec isa (withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv)) s t u) :
    ∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 2584, 2584⟩ : Region).Contains x 1 →
      u.mem x = (loseL (s.gpr .rsp - BitVec.ofNat 64 2584) 2584
        (innerU (streamEncryptClr (v.withBlk B) lv) (narrowS Spec.Gcm.streamCryptSig .u64 320 2584 s)) (streamFV Lb s) x).getD (s.mem x) := by
  have hsp := streamEncryptSM_spSafe (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_all lv] at hsp
  have hd := streamEncryptSM_xdepth (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_x86_64Depth lv] at hd
  exact framedS_leaves (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (leak := none) (P := Proof.AesGcm.streamEncryptX86_64.pre)
    (Verified.hoist lv (streamEncryptSB_verified (v.wrapC lv) (B.wrapC lv))) (fun s h => streamEncryptS_implies.pre s h)
    (fun s t s' hp he => by
      obtain ⟨t', s'', e', q⟩ := streamS_leaves (v.wrapC lv) (B.wrapC lv) (gf.wrapC lv) (cf.wrapC lv) true
        (hL.wrapC lv) (M := CtxMode.base) hp trivial
      obtain ⟨-, rfl⟩ := Exec.det ((exec_hoist lv _ _ _ _).mp he) e'
      exact q)
    rfl (by decide) (by decide) hsp hd (streamTextPre_local _) hs he

omit gf cf in
/-- What `streamEncryptClrB_leaves` leaves goes through the release of the frame with the
unknowns its code ends with, which two runs agree on. -/
theorem streamEncryptClrB_leaves_innerU (B : BlkFn CtxMode.base) {s₁ s₂ : State}
    (h₁ : (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608).pre s₁) (h₂ : (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608).pre s₂)
    (hp : (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608).pub s₁ s₂) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (streamEncryptClr (v.withBlk B) lv), s₁.syms n = s₂.syms n) :
    innerU (streamEncryptClr (v.withBlk B) lv) (narrowS Spec.Gcm.streamCryptSig .u64 320 2584 s₁) =
      innerU (streamEncryptClr (v.withBlk B) lv) (narrowS Spec.Gcm.streamCryptSig .u64 320 2584 s₂) :=
  framed_innerU_agree (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits) (wa := true) (leak := none)
    (Verified.hoist lv (streamEncryptSB_verified (v.wrapC lv) (B.wrapC lv))) (by decide) (by decide) (by decide) (streamTextPre_local _) h₁ h₂ hp hu hsy

/-- `streamEncryptClrB_leaves` for `vg_aes_gcm_stream_decrypt`. -/
theorem streamDecryptClrB_leaves (B : BlkFn CtxMode.base)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb B.dec.code CtxMode.base) {s : State}
    (hs : (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608).pre s) {t : List Leak} {u : State}
    (he : Exec isa (withStackArgScratch 2584 1 (streamDecryptClr (v.withBlk B) lv)) s t u) :
    ∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 2584, 2584⟩ : Region).Contains x 1 →
      u.mem x = (loseL (s.gpr .rsp - BitVec.ofNat 64 2584) 2584
        (innerU (streamDecryptClr (v.withBlk B) lv) (narrowS Spec.Gcm.streamCryptSig .u64 320 2584 s)) (streamFV Lb s) x).getD (s.mem x) := by
  have hsp := streamDecryptSM_spSafe (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_all lv] at hsp
  have hd := streamDecryptSM_xdepth (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_x86_64Depth lv] at hd
  exact framedS_leaves (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (leak := none) (P := Proof.AesGcm.streamDecryptX86_64.pre)
    (Verified.hoist lv (streamDecryptSB_verified (v.wrapC lv) (B.wrapC lv))) (fun s h => streamDecryptS_implies.pre s h)
    (fun s t s' hp he => by
      obtain ⟨t', s'', e', q⟩ := streamS_leaves (v.wrapC lv) (B.wrapC lv) (gf.wrapC lv) (cf.wrapC lv) false
        (hL.wrapC lv) (M := CtxMode.base) hp trivial
      obtain ⟨-, rfl⟩ := Exec.det ((exec_hoist lv _ _ _ _).mp he) e'
      exact q)
    rfl (by decide) (by decide) hsp hd (streamTextPre_local _) hs he

omit gf cf in
/-- What `streamDecryptClrB_leaves` leaves goes through the release of the frame with the
unknowns its code ends with, which two runs agree on. -/
theorem streamDecryptClrB_leaves_innerU (B : BlkFn CtxMode.base) {s₁ s₂ : State}
    (h₁ : (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608).pre s₁) (h₂ : (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608).pre s₂)
    (hp : (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608).pub s₁ s₂) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (streamDecryptClr (v.withBlk B) lv), s₁.syms n = s₂.syms n) :
    innerU (streamDecryptClr (v.withBlk B) lv) (narrowS Spec.Gcm.streamCryptSig .u64 320 2584 s₁) =
      innerU (streamDecryptClr (v.withBlk B) lv) (narrowS Spec.Gcm.streamCryptSig .u64 320 2584 s₂) :=
  framed_innerU_agree (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits) (wa := true) (leak := none)
    (Verified.hoist lv (streamDecryptSB_verified (v.wrapC lv) (B.wrapC lv))) (by decide) (by decide) (by decide) (streamTextPre_local _) h₁ h₂ hp hu hsy

omit gf cf in
/-- `vg_aes_gcm_stream_encrypt` clearing the registers after each call, with
callees that never touch their working space and a blocks function that
leaves `Lb` in its `scratch`: what it leaves in its frame (`streamFV`). -/
theorem streamEncryptClrB_leavesZ (B : BlkFn CtxMode.base) {zg : Nat → Bool} (GZ : GhCallZ (v.wrapC lv) zg) {sc : Nat} {z : Nat → Bool} (hsc : sc ≤ 2048) (CZ : CrCallZ (v.wrapC lv) sc z)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb B.enc.code CtxMode.base) {s : State}
    (hs : (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608).pre s) {t : List Leak} {u : State}
    (he : Exec isa (withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv)) s t u) :
    ∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 2584, 2584⟩ : Region).Contains x 1 →
      u.mem x = (loseL (s.gpr .rsp - BitVec.ofNat 64 2584) 2584
        (innerU (streamEncryptClr (v.withBlk B) lv) (narrowS Spec.Gcm.streamCryptSig .u64 320 2584 s)) (streamFVZ z zg Lb s) x).getD (s.mem x) := by
  have hsp := streamEncryptSM_spSafe (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_all lv] at hsp
  have hd := streamEncryptSM_xdepth (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_x86_64Depth lv] at hd
  exact framedS_leavesZ (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (leak := none) (P := Proof.AesGcm.streamEncryptX86_64.pre)
    (Verified.hoist lv (streamEncryptSB_verified (v.wrapC lv) (B.wrapC lv))) (fun s h => streamEncryptS_implies.pre s h)
    (fun s t s' hp he => by
      obtain ⟨t', s'', e', q⟩ := streamS_leavesZ (v.wrapC lv) (B.wrapC lv) GZ hsc CZ true
        (hL.wrapC lv) (M := CtxMode.base) hp trivial
      obtain ⟨-, rfl⟩ := Exec.det ((exec_hoist lv _ _ _ _).mp he) e'
      exact q)
    rfl (by decide) (by decide) hsp hd (streamTextPre_local _) hs he

omit gf cf in
/-- `streamEncryptClrB_leavesZ` for `vg_aes_gcm_stream_decrypt`. -/
theorem streamDecryptClrB_leavesZ (B : BlkFn CtxMode.base) {zg : Nat → Bool} (GZ : GhCallZ (v.wrapC lv) zg) {sc : Nat} {z : Nat → Bool} (hsc : sc ≤ 2048) (CZ : CrCallZ (v.wrapC lv) sc z)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb B.dec.code CtxMode.base) {s : State}
    (hs : (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608).pre s) {t : List Leak} {u : State}
    (he : Exec isa (withStackArgScratch 2584 1 (streamDecryptClr (v.withBlk B) lv)) s t u) :
    ∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 2584, 2584⟩ : Region).Contains x 1 →
      u.mem x = (loseL (s.gpr .rsp - BitVec.ofNat 64 2584) 2584
        (innerU (streamDecryptClr (v.withBlk B) lv) (narrowS Spec.Gcm.streamCryptSig .u64 320 2584 s)) (streamFVZ z zg Lb s) x).getD (s.mem x) := by
  have hsp := streamDecryptSM_spSafe (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_all lv] at hsp
  have hd := streamDecryptSM_xdepth (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_x86_64Depth lv] at hd
  exact framedS_leavesZ (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (leak := none) (P := Proof.AesGcm.streamDecryptX86_64.pre)
    (Verified.hoist lv (streamDecryptSB_verified (v.wrapC lv) (B.wrapC lv))) (fun s h => streamDecryptS_implies.pre s h)
    (fun s t s' hp he => by
      obtain ⟨t', s'', e', q⟩ := streamS_leavesZ (v.wrapC lv) (B.wrapC lv) GZ hsc CZ false
        (hL.wrapC lv) (M := CtxMode.base) hp trivial
      obtain ⟨-, rfl⟩ := Exec.det ((exec_hoist lv _ _ _ _).mp he) e'
      exact q)
    rfl (by decide) (by decide) hsp hd (streamTextPre_local _) hs he

/-- `streamEncryptClrB_leaves`, on 16 powers of the hash subkey. -/
theorem streamEncryptClr16_leaves (B : BlkFn CtxMode.prepared16)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb B.enc.code CtxMode.prepared16) {s : State}
    (hs : (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608).pre s) {t : List Leak} {u : State}
    (he : Exec isa (withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv)) s t u) :
    ∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 2584, 2584⟩ : Region).Contains x 1 →
      u.mem x = (loseL (s.gpr .rsp - BitVec.ofNat 64 2584) 2584
        (innerU (streamEncryptClr (v.withBlk B) lv) (narrowS Proof.Gcm.streamCryptPrecomputedSig .u64 320 2584 s)) (streamFV Lb s) x).getD (s.mem x) := by
  have hsp := streamEncryptSM_spSafe (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_all lv] at hsp
  have hd := streamEncryptSM_xdepth (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_x86_64Depth lv] at hd
  exact framedS_leaves (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Proof.Gcm.streamCryptPrepared16Pre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (leak := none) (P := (Proof.AesGcm.streamEncryptX86_64M CtxMode.prepared16).pre)
    (Verified.hoist lv (streamEncryptSPrepared16_verified (v.wrapC lv) (B.wrapC lv)))
    (fun s h => streamEncryptSPrepared16_implies.pre s h)
    (fun s t s' hp he => by
      obtain ⟨t', s'', e', q⟩ := streamS_leaves (v.wrapC lv) (B.wrapC lv) (gf.wrapC lv) (cf.wrapC lv) true
        (hL.wrapC lv) hp.1 hp.2
      obtain ⟨-, rfl⟩ := Exec.det ((exec_hoist lv _ _ _ _).mp he) e'
      exact q)
    rfl (by decide) (by decide) hsp hd (Proof.AesGcm.streamCryptPrepared16Pre_local _) hs he

omit gf cf in
/-- What `streamEncryptClr16_leaves` leaves goes through the release of the frame with the
unknowns its code ends with, which two runs agree on. -/
theorem streamEncryptClr16_leaves_innerU (B : BlkFn CtxMode.prepared16) {s₁ s₂ : State}
    (h₁ : (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608).pre s₁) (h₂ : (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608).pre s₂)
    (hp : (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608).pub s₁ s₂) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (streamEncryptClr (v.withBlk B) lv), s₁.syms n = s₂.syms n) :
    innerU (streamEncryptClr (v.withBlk B) lv) (narrowS Proof.Gcm.streamCryptPrecomputedSig .u64 320 2584 s₁) =
      innerU (streamEncryptClr (v.withBlk B) lv) (narrowS Proof.Gcm.streamCryptPrecomputedSig .u64 320 2584 s₂) :=
  framed_innerU_agree (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Proof.Gcm.streamCryptPrepared16Pre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits) (wa := true) (leak := none)
    (Verified.hoist lv (streamEncryptSPrepared16_verified (v.wrapC lv) (B.wrapC lv))) (by decide) (by decide) (by decide) (Proof.AesGcm.streamCryptPrepared16Pre_local _) h₁ h₂ hp hu hsy

/-- `streamEncryptClr16_leaves` for `vg_aes_gcm_stream_decrypt`. -/
theorem streamDecryptClr16_leaves (B : BlkFn CtxMode.prepared16)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb B.dec.code CtxMode.prepared16) {s : State}
    (hs : (Proof.AesGcm.streamDecryptPrepared16RoundsContract X86_64.abi 2608).pre s) {t : List Leak} {u : State}
    (he : Exec isa (withStackArgScratch 2584 1 (streamDecryptClr (v.withBlk B) lv)) s t u) :
    ∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 2584, 2584⟩ : Region).Contains x 1 →
      u.mem x = (loseL (s.gpr .rsp - BitVec.ofNat 64 2584) 2584
        (innerU (streamDecryptClr (v.withBlk B) lv) (narrowS Proof.Gcm.streamCryptPrecomputedSig .u64 320 2584 s)) (streamFV Lb s) x).getD (s.mem x) := by
  have hsp := streamDecryptSM_spSafe (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_all lv] at hsp
  have hd := streamDecryptSM_xdepth (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_x86_64Depth lv] at hd
  exact framedS_leaves (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Proof.Gcm.streamCryptPrepared16Pre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (leak := none) (P := (Proof.AesGcm.streamDecryptX86_64M CtxMode.prepared16).pre)
    (Verified.hoist lv (streamDecryptSPrepared16_verified (v.wrapC lv) (B.wrapC lv)))
    (fun s h => streamDecryptSPrepared16_implies.pre s h)
    (fun s t s' hp he => by
      obtain ⟨t', s'', e', q⟩ := streamS_leaves (v.wrapC lv) (B.wrapC lv) (gf.wrapC lv) (cf.wrapC lv) false
        (hL.wrapC lv) hp.1 hp.2
      obtain ⟨-, rfl⟩ := Exec.det ((exec_hoist lv _ _ _ _).mp he) e'
      exact q)
    rfl (by decide) (by decide) hsp hd (Proof.AesGcm.streamCryptPrepared16Pre_local _) hs he

omit gf cf in
/-- What `streamDecryptClr16_leaves` leaves goes through the release of the frame with the
unknowns its code ends with, which two runs agree on. -/
theorem streamDecryptClr16_leaves_innerU (B : BlkFn CtxMode.prepared16) {s₁ s₂ : State}
    (h₁ : (Proof.AesGcm.streamDecryptPrepared16RoundsContract X86_64.abi 2608).pre s₁) (h₂ : (Proof.AesGcm.streamDecryptPrepared16RoundsContract X86_64.abi 2608).pre s₂)
    (hp : (Proof.AesGcm.streamDecryptPrepared16RoundsContract X86_64.abi 2608).pub s₁ s₂) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (streamDecryptClr (v.withBlk B) lv), s₁.syms n = s₂.syms n) :
    innerU (streamDecryptClr (v.withBlk B) lv) (narrowS Proof.Gcm.streamCryptPrecomputedSig .u64 320 2584 s₁) =
      innerU (streamDecryptClr (v.withBlk B) lv) (narrowS Proof.Gcm.streamCryptPrecomputedSig .u64 320 2584 s₂) :=
  framed_innerU_agree (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Proof.Gcm.streamCryptPrepared16Pre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits) (wa := true) (leak := none)
    (Verified.hoist lv (streamDecryptSPrepared16_verified (v.wrapC lv) (B.wrapC lv))) (by decide) (by decide) (by decide) (Proof.AesGcm.streamCryptPrepared16Pre_local _) h₁ h₂ hp hu hsy

/-- `streamEncryptClrB_leaves`, on 48 powers of the hash subkey. -/
theorem streamEncryptClr48_leaves (B : BlkFn CtxMode.prepared)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb B.enc.code CtxMode.prepared) {s : State}
    (hs : (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608).pre s) {t : List Leak} {u : State}
    (he : Exec isa (withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv)) s t u) :
    ∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 2584, 2584⟩ : Region).Contains x 1 →
      u.mem x = (loseL (s.gpr .rsp - BitVec.ofNat 64 2584) 2584
        (innerU (streamEncryptClr (v.withBlk B) lv) (narrowS Proof.Gcm.streamCryptPrecomputedSig .u64 320 2584 s)) (streamFV Lb s) x).getD (s.mem x) := by
  have hsp := streamEncryptSM_spSafe (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_all lv] at hsp
  have hd := streamEncryptSM_xdepth (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_x86_64Depth lv] at hd
  exact framedS_leaves (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Proof.Gcm.streamCryptPowersPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (leak := none) (P := (Proof.AesGcm.streamEncryptX86_64M CtxMode.prepared).pre)
    (Verified.hoist lv (streamEncryptSPrepared_verified (v.wrapC lv) (B.wrapC lv)))
    (fun s h => streamEncryptSPrepared_implies.pre s h)
    (fun s t s' hp he => by
      obtain ⟨t', s'', e', q⟩ := streamS_leaves (v.wrapC lv) (B.wrapC lv) (gf.wrapC lv) (cf.wrapC lv) true
        (hL.wrapC lv) hp.1 hp.2
      obtain ⟨-, rfl⟩ := Exec.det ((exec_hoist lv _ _ _ _).mp he) e'
      exact q)
    rfl (by decide) (by decide) hsp hd (Proof.AesGcm.streamCryptPreparedPre_local _) hs he

omit gf cf in
/-- What `streamEncryptClr48_leaves` leaves goes through the release of the frame with the
unknowns its code ends with, which two runs agree on. -/
theorem streamEncryptClr48_leaves_innerU (B : BlkFn CtxMode.prepared) {s₁ s₂ : State}
    (h₁ : (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608).pre s₁) (h₂ : (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608).pre s₂)
    (hp : (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608).pub s₁ s₂) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (streamEncryptClr (v.withBlk B) lv), s₁.syms n = s₂.syms n) :
    innerU (streamEncryptClr (v.withBlk B) lv) (narrowS Proof.Gcm.streamCryptPrecomputedSig .u64 320 2584 s₁) =
      innerU (streamEncryptClr (v.withBlk B) lv) (narrowS Proof.Gcm.streamCryptPrecomputedSig .u64 320 2584 s₂) :=
  framed_innerU_agree (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Proof.Gcm.streamCryptPowersPre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits) (wa := true) (leak := none)
    (Verified.hoist lv (streamEncryptSPrepared_verified (v.wrapC lv) (B.wrapC lv))) (by decide) (by decide) (by decide) (Proof.AesGcm.streamCryptPreparedPre_local _) h₁ h₂ hp hu hsy

/-- `streamEncryptClr48_leaves` for `vg_aes_gcm_stream_decrypt`. -/
theorem streamDecryptClr48_leaves (B : BlkFn CtxMode.prepared)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb B.dec.code CtxMode.prepared) {s : State}
    (hs : (Proof.AesGcm.streamDecryptPreparedRoundsContract X86_64.abi 2608).pre s) {t : List Leak} {u : State}
    (he : Exec isa (withStackArgScratch 2584 1 (streamDecryptClr (v.withBlk B) lv)) s t u) :
    ∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 2584, 2584⟩ : Region).Contains x 1 →
      u.mem x = (loseL (s.gpr .rsp - BitVec.ofNat 64 2584) 2584
        (innerU (streamDecryptClr (v.withBlk B) lv) (narrowS Proof.Gcm.streamCryptPrecomputedSig .u64 320 2584 s)) (streamFV Lb s) x).getD (s.mem x) := by
  have hsp := streamDecryptSM_spSafe (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_all lv] at hsp
  have hd := streamDecryptSM_xdepth (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_x86_64Depth lv] at hd
  exact framedS_leaves (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Proof.Gcm.streamCryptPowersPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (leak := none) (P := (Proof.AesGcm.streamDecryptX86_64M CtxMode.prepared).pre)
    (Verified.hoist lv (streamDecryptSPrepared_verified (v.wrapC lv) (B.wrapC lv)))
    (fun s h => streamDecryptSPrepared_implies.pre s h)
    (fun s t s' hp he => by
      obtain ⟨t', s'', e', q⟩ := streamS_leaves (v.wrapC lv) (B.wrapC lv) (gf.wrapC lv) (cf.wrapC lv) false
        (hL.wrapC lv) hp.1 hp.2
      obtain ⟨-, rfl⟩ := Exec.det ((exec_hoist lv _ _ _ _).mp he) e'
      exact q)
    rfl (by decide) (by decide) hsp hd (Proof.AesGcm.streamCryptPreparedPre_local _) hs he

omit gf cf in
/-- What `streamDecryptClr48_leaves` leaves goes through the release of the frame with the
unknowns its code ends with, which two runs agree on. -/
theorem streamDecryptClr48_leaves_innerU (B : BlkFn CtxMode.prepared) {s₁ s₂ : State}
    (h₁ : (Proof.AesGcm.streamDecryptPreparedRoundsContract X86_64.abi 2608).pre s₁) (h₂ : (Proof.AesGcm.streamDecryptPreparedRoundsContract X86_64.abi 2608).pre s₂)
    (hp : (Proof.AesGcm.streamDecryptPreparedRoundsContract X86_64.abi 2608).pub s₁ s₂) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (streamDecryptClr (v.withBlk B) lv), s₁.syms n = s₂.syms n) :
    innerU (streamDecryptClr (v.withBlk B) lv) (narrowS Proof.Gcm.streamCryptPrecomputedSig .u64 320 2584 s₁) =
      innerU (streamDecryptClr (v.withBlk B) lv) (narrowS Proof.Gcm.streamCryptPrecomputedSig .u64 320 2584 s₂) :=
  framed_innerU_agree (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Proof.Gcm.streamCryptPowersPre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits) (wa := true) (leak := none)
    (Verified.hoist lv (streamDecryptSPrepared_verified (v.wrapC lv) (B.wrapC lv))) (by decide) (by decide) (by decide) (Proof.AesGcm.streamCryptPreparedPre_local _) h₁ h₂ hp hu hsy

end

end VG.Proof.AesGcm.X86_64
