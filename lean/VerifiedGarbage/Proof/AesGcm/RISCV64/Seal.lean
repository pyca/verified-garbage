module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Tag
public import VerifiedGarbage.Proof.AesGcm.RISCV64.J0
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Crypt
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Run

/-! ### `AesGcm.RISCV64.OneShot`, which this module and modules that import it used -/

section

/-!
# AES-GCM on RISC-V: the pieces of `vg_aes_gcm_seal` and `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTCrypt.lean`): both keep a streaming state at `W + 16`;
`oneAad` writes `J₀` and absorbs the additional data, padded (`oneAad_ok`),
`oneCrypt` runs counter mode over the data from the first counter block
(`oneCrypt_ok`), and `oneTag o` absorbs the data as ciphertext, padded, then
the lengths block, and writes the tag to `W + o` (`oneTag_ok`). The pieces
are stated for an environment `Env V sp s`, whose registers the entries of
`seal` and `open` fill, and the addresses of the additional data and the
data, `A` and `D`, which they keep in `W` (at `aadO` and `dataO`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput zeros padLen j0 inc32 gctr ghash ghashFrom blocks toBytes ofBytes)
open VG.Proof.Gcm (Absorbed Ctr lensBlock padded)

theorem abs16_j0 {st w sp : Addr} : ∀ r ∈ absFrame st w 16 sp, ∃ r' ∈ j0Frame st w sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem t16_j0 {st w sp : Addr} : ∀ r ∈ tFrame st w 16 sp, ∃ r' ∈ j0Frame st w sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- A buffer apart from the state, `W` and the stack is apart from what `j0` writes. -/
theorem data_j0 {st w : Addr} {s : State} {D : Addr} {n : Nat} (hd : DataOk st w s D n) {sp : Addr}
    (hsp : s.sp = sp) : ∀ r ∈ j0Frame st w sp, (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.st
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hsp ▸ hd.sk

/-- The buffer of the bitsliced round keys is apart from what `j0` writes. -/
theorem BkIn.j0Frame {B c st w sp : Addr} {R : Nat} {m₀ : Mem} {S D : Addr} {n : Nat} {s : State}
    (hb : BkIn B c st w sp R m₀ S D n s) : ∀ r ∈ j0Frame st w sp, (⟨B, 960⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hb.st
  · exact hb.w.sub_right (Lay.wSub (by decide))
  · exact hb.w.sub_right (Lay.wSub (by decide))
  · exact hb.sk

/-- The context is apart from what `j0` writes. -/
theorem ctx_j0Frame {c st w sp : Addr} (L : Lay c st w) (hk : StkOk c st w sp) :
    ∀ r ∈ j0Frame st w sp, (⟨c, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.cs
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact hk.c

/-- The bitsliced round keys, after code whose frame is within `j0`'s. -/
theorem BkIn.frameJ0 {B c st w sp : Addr} {R : Nat} {m m' : Mem} {S D : Addr} {n : Nat} {s s' : State}
    (hb : BkIn B c st w sp R m S D n s) (L : Lay c st w) (hk : StkOk c st w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {rs : List Region} (hf : Frame rs m m') (hj : ∀ r ∈ rs, ∃ r' ∈ RISCV64.j0Frame st w sp, Region.Sub r r')
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : BkIn B c st w sp R m' S D n s' :=
  hb.frame hR hf (fun r hr => let ⟨r', hr', h⟩ := hj r hr; (hb.j0Frame r' hr').sub_right h)
    (fun r hr => let ⟨r', hr', h⟩ := hj r hr; (ctx_j0Frame L hk r' hr').sub_right h) hrd hwr

/-- A doubleword apart from a frame's regions keeps its value. -/
theorem slot_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : m'.readW p 64 = m.readW p 64 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-- After `oneAad`, from `m₀`: `J₀` of `iv`, the first counter block, and the
additional data `a` absorbed and padded. -/
structure OA (V : Reg → BitVec 64) (sp : Addr) (H : Block) (iv a : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H
  j : blockAt s.mem (V .s1) = j0 H iv
  cb : blockAt s.mem (V .s1 + BitVec.ofNat 64 48) = inc32 (j0 H iv)
  abs : Absorbed s.mem (V .s1 + BitVec.ofNat 64 16) (V .s1 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length))
  frame : Frame (j0Frame (V .s1) (V .s0) sp) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0))
include L

/-- The counter blocks are apart from what `absorb 16` and `flush 16` write. -/
theorem stb_abs16 (hk : StkOk (V .s2) (V .s1) (V .s0) sp) {d : Nat} (hd : d = 0 ∨ d = 48) :
    ∀ r ∈ absFrame (V .s1) (V .s0) 16 sp, (⟨V .s1 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega_using [hd]) (by omega_using [hd]) (by decide)
  · exact Lay.st_st (by omega_using [hd]) (by omega_using [hd]) (by decide)
  · exact L.st_w (by omega_using [hd]) (.inr ⟨by decide, by decide⟩)
  · exact hk.st.sub_left (Lay.stSub (by omega_using [hd]))

theorem stb_t16 (hk : StkOk (V .s2) (V .s1) (V .s0) sp) {d : Nat} (hd : d = 0 ∨ d = 48) :
    ∀ r ∈ tFrame (V .s1) (V .s0) 16 sp, (⟨V .s1 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega_using [hd]) (by omega_using [hd]) (by decide)
  · exact L.st_w (by omega_using [hd]) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by omega_using [hd]) (.inr ⟨by decide, by decide⟩)
  · exact hk.st.sub_left (Lay.stSub (by omega_using [hd]))

/-- The slots of `W` from 232 to 256, which hold the addresses of the
additional data and the data (and, out of place, the distance to the
destination), are apart from what `j0` writes. -/
theorem slot_j0' (hk : StkOk (V .s2) (V .s1) (V .s0) sp) {d : Nat} (hd : 232 ≤ d ∧ d + 8 ≤ 256) :
    ∀ r ∈ j0Frame (V .s1) (V .s0) sp, (⟨V .s0 + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 80) (d := d) (k := 8) (by decide) (.inr ⟨by omega_using [hd], by omega_using [hd]⟩)).symm
  · exact Lay.w_w (by omega_using [hd]) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (by omega_using [hd]) (by omega_using [hd]) (by decide)
  · exact hk.w.sub_left (Lay.wSub (by omega_using [hd]))

theorem slot_j0 (hk : StkOk (V .s2) (V .s1) (V .s0) sp) {d : Nat} (hd : 232 ≤ d ∧ d + 8 ≤ 248) :
    ∀ r ∈ j0Frame (V .s1) (V .s0) sp, (⟨V .s0 + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r :=
  slot_j0' L hk ⟨hd.1, by omega_using [hd]⟩

theorem slot_abs (hk : StkOk (V .s2) (V .s1) (V .s0) sp) {d : Nat} (hd : 232 ≤ d ∧ d + 8 ≤ 248) :
    ∀ r ∈ absFrame (V .s1) (V .s0) 16 sp, (⟨V .s0 + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r :=
  fun r hr => by
    obtain ⟨r', hr', hs⟩ := abs16_j0 r hr
    exact (slot_j0 L hk hd r' hr').sub_right hs

theorem slot_t (hk : StkOk (V .s2) (V .s1) (V .s0) sp) {d : Nat} (hd : 232 ≤ d ∧ d + 8 ≤ 248) :
    ∀ r ∈ tFrame (V .s1) (V .s0) 16 sp, (⟨V .s0 + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r :=
  fun r hr => by
    obtain ⟨r', hr', hs⟩ := t16_j0 r hr
    exact (slot_j0 L hk hd r' hr').sub_right hs

/-- The slots of the addresses are apart from what `crypt` writes. -/
theorem slot_crFrame' {s : State} {D : Addr} {n : Nat} (hd : DataW (V .s2) (V .s1) (V .s0) s D n) {d : Nat}
    (hdd : 232 ≤ d ∧ d + 8 ≤ 256) :
    ∀ r ∈ crFrame (V .s1) (V .s0) D n, (⟨V .s0 + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by omega_using [hdd]))).symm
  · exact (L.st_w (by decide) (.inr ⟨by omega_using [hdd], by omega_using [hdd]⟩)).symm
  · exact Lay.w_w (.inl (by omega_using [hdd])) (by omega_using [hdd]) (by decide)

theorem slot_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW (V .s2) (V .s1) (V .s0) s D n) {d : Nat}
    (hdd : 232 ≤ d ∧ d + 8 ≤ 248) :
    ∀ r ∈ crFrame (V .s1) (V .s0) D n, (⟨V .s0 + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r :=
  slot_crFrame' L hd ⟨hdd.1, by omega_using [hdd]⟩

/-- `oneAad`: `J₀` of the `n`-byte nonce at `Np`, then the additional data
(`aad_len`, `s10`, bytes at `A`, in `W + aadO`) absorbed and padded. -/
theorem oneAad_ok [VG.Proof.Gcm.RISCV64.GhashLaw] {H : Block} {Np A : Addr} {n : Nat} {s : State} (he : Env V sp s)
    (hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H) (h24 : s.gpr .s4 = Np)
    (h25 : s.gpr .s5 = BitVec.ofNat 64 n) (h18 : V .s7 = BitVec.ofNat 64 n) (hN : DataOk (V .s1) (V .s0) s Np n)
    (hA : DataOk (V .s1) (V .s0) s A (V .s10).toNat)
    (hAs : s.mem.readW (V .s0 + BitVec.ofNat 64 aadO) 64 = A) :
    WP isa oneAad s (OA V sp H (bytesAt s.mem Np n) (bytesAt s.mem A (V .s10).toNat) s.mem) := by
  have hk := he.stk'
  refine WP.seq (WP.mono (WP.with_rdwr (j0_ok L ⟨he, hH, h24, h25, h18, hN⟩)) fun s₂ ⟨jo, rd₂, wr₂, sp₂⟩ => ?_)
  have h22 := jo.env.ofNat (r := .s10) (by decide)
  have hA₂ : s₂.mem.readW (V .s0 + BitVec.ofNat 64 aadO) 64 = A := by
    rw [slot_keep jo.frame (slot_j0 L hk (by decide)), hAs]
  have h₃ : WP isa (.block [.load .d .s4 .s0 aadO, mov .s5 .s10, .li .s6 0]) s₂ fun s₃ =>
      s₃.gpr .s4 = A ∧ s₃.gpr .s5 = BitVec.ofNat 64 (V .s10).toNat ∧ s₃.gpr .s6 = BitVec.ofNat 64 0 ∧
        (∀ r, r ≠ .s4 → r ≠ .s5 → r ≠ .s6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    refine Steps.wp_ld (off := aadO) (a := V .s0 + BitVec.ofNat 64 aadO) (by decide) (by rw [jo.env.s0])
      (L.wal8 (by decide) (by decide)) (jo.env.perm.wR (by decide)) fun s₃ u₃ => ?_
    refine Steps.wp_mv fun s₄ u₄ => Steps.wp_li (imm := 0) (by decide) fun s₅ u₅ => WP.block_nil ?_
    refine ⟨by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, hA₂], by
      rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), h22], u₅.gpr, fun r a b c => by
      rw [u₅.other _ c, u₄.other _ b, u₃.other _ a], ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [u₅.mem, u₄.mem, u₃.mem]
    · rw [u₅.rd, u₄.rd, u₃.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr]
    · rw [u₅.sp, u₄.sp, u₃.sp]
  refine WP.seq (WP.mono h₃ fun s₃ ⟨a24, a25, a26, g₃, k₃⟩ => ?_)
  have he₃ := jo.env.keep (fun r hr => g₃ r (by revert r; decide) (by revert r; decide) (by revert r; decide))
    k₃.sp k₃.rd k₃.wr
  have hAm : bytesAt s₃.mem A (V .s10).toNat = bytesAt s.mem A (V .s10).toNat := by
    rw [k₃.mem]; exact bytesAt_frame jo.frame (data_j0 hA he.sp) (by have := hA.lt; omega_using [])
  have ai : AbsIn V sp 16 H [] A (V .s10).toNat s₃ :=
    ⟨he₃, a24, a25, by rw [a26]; rfl, hA.of_eq (k₃.rd.trans rd₂) (k₃.wr.trans wr₂) (k₃.sp.trans sp₂),
      by rw [k₃.mem]; exact jo.hH⟩
  refine WP.seq (WP.mono (absorb_ok L (.inr rfl) ai) fun s₄ ab => ?_)
  rw [hAm, List.nil_append] at ab
  have h22' := ab.env.fr .s10 (by decide)
  have hand := and15 (V .s10)
  have h₅ : WP isa (.block [.logicImm .and .s6 .s10 15]) s₄ fun s₅ =>
      s₅.gpr .s6 = BitVec.ofNat 64 ((V .s10).toNat % 16) ∧
        (∀ r, r ≠ .s6 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    crun [Int.reduceNatCast', h22', hand]
    exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₅ fun s₅ ⟨a26', g₅, k₅⟩ => ?_)
  have he₅ := ab.env.keep (fun r hr => g₅ r (by revert r; decide)) k₅.sp k₅.rd k₅.wr
  have hH₄ : blockAt s₄.mem (V .s2 + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl) hk), k₃.mem]; exact jo.hH
  refine WP.mono (flush_ok L (yo := 16) (.inr rfl) (x := bytesAt s.mem A (V .s10).toNat) (H := H)
    ⟨he₅, by rw [k₅.mem]; exact hH₄⟩ (by rw [a26', length_bytesAt])) fun s₆ fl => ?_
  have flf := fl.frame
  rw [k₅.mem] at flf
  have abf := ab.frame
  rw [k₃.mem] at abf
  have blk : ∀ {d : Nat}, (d = 0 ∨ d = 48) → blockAt s₆.mem (V .s1 + BitVec.ofNat 64 d) =
      blockAt s₂.mem (V .s1 + BitVec.ofNat 64 d) := fun hd => by
    rw [blockAt_frame flf (stb_t16 L hk hd), blockAt_frame abf (stb_abs16 L hk hd)]
  refine ⟨fl.env, fl.hH, ?_, ?_, fl.abs (by rw [k₅.mem]; exact ab.abs (by
    rw [k₃.mem]; exact Proof.Gcm.absorbed_nil _ jo.y)), ?_⟩
  · have := blk (d := 0) (.inl rfl); rw [BitVec.add_zero] at this; rw [this]; exact jo.j0
  · rw [blk (.inr rfl)]; exact jo.cb
  · exact (jo.frame.trans (abf.sub abs16_j0)).trans (flf.sub t16_j0)

end

/-- After `oneCryptWith o`, from `m₀`: the data at `S` decrypted to `D`. -/
structure OC (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (icb : Block) (S D : Addr) (m₀ : Mem) (s : State) :
    Prop where
  env : Env V sp s
  out : bytesAt s.mem D (V .s11).toNat = gctr (ciphOf m₀ (V .s2) R) icb (bytesAt m₀ S (V .s11).toNat)
  frame : Frame (crFrame (V .s1) (V .s0) D (V .s11).toNat) m₀ s.mem

theorem dataArgs_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s)
    (hal : (V .s0).toNat % 8 = 0) {D : Addr} (hDs : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D) :
    WP isa (.block dataArgs) s fun s' =>
      s'.gpr .s4 = D ∧ s'.gpr .s5 = BitVec.ofNat 64 (V .s11).toNat ∧ s'.gpr .s6 = BitVec.ofNat 64 0 ∧
        (∀ r, r ≠ .s4 → r ≠ .s5 → r ≠ .s6 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h23 := he.ofNat (r := .s11) (by decide)
  simp only [dataArgs]
  refine Steps.wp_ld (off := dataO) (a := V .s0 + BitVec.ofNat 64 dataO) (by decide) (by rw [he.s0])
    (Spill.al8 hal (by decide)) (he.perm.wR (by decide)) fun s₃ u₃ => ?_
  refine Steps.wp_mv fun s₄ u₄ => Steps.wp_li (imm := 0) (by decide) fun s₅ u₅ => WP.block_nil ?_
  refine ⟨by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, hDs], by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), h23], u₅.gpr, fun r a b c => by
    rw [u₅.other _ c, u₄.other _ b, u₃.other _ a], ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [u₅.mem, u₄.mem, u₃.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp]

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0))
include L

/-- `oneCryptWith o`: counter mode over the data (`len`, `s11`, bytes at `S`,
in `W + dataO`), to `D` (`S` in place), from the counter block `icb`. -/
theorem oneCryptB_ok {bs o : Bool} {R : Nat} {S D : Addr} {s : State} (he : Env V sp s)
    (h28 : V .s3 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hd : DataW (V .s2) (V .s1) (V .s0) s D (V .s11).toNat) (hs : DataOk (V .s1) (V .s0) s S (V .s11).toNat)
    (ha : Alias o S D (V .s11).toNat)
    (hδ : o = true → V .s9 = D - S)
    (hDs : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = S)
    {icb : Block} (hcb : blockAt s.mem (V .s1 + BitVec.ofNat 64 48) = icb)
    (hb : bs = true → BkIn (V .s7) (V .s2) (V .s1) (V .s0) sp R s.mem S D (V .s11).toNat s) :
    WP isa (oneCryptB bs o) s (OC V sp R icb S D s.mem) := by
  refine WP.seq (WP.mono (dataArgs_ok he L.wal hDs) fun s₁ ⟨a24, a25, a26, g₁, k₁⟩ => ?_)
  have he₁ := he.keep (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide))
    k₁.sp k₁.rd k₁.wr
  have ci : CrIn o V sp R icb 0 S D (V .s11).toNat s₁ :=
    ⟨he₁, a24, a25, by rw [a26], h28, hR, hd.of_eq k₁.rd k₁.wr k₁.sp, hs.of_eq k₁.rd k₁.wr k₁.sp, ha,
      hδ⟩
  refine WP.mono (cryptB_ok L ci fun hbs => ((hb hbs).of_eq k₁.rd k₁.wr).memEq k₁.mem) fun s₂ co => ?_
  rw [k₁.mem] at co
  have c0 := Proof.Gcm.ctr_zero s.mem _ (V .s1 + BitVec.ofNat 64 64) (ciphOf s.mem (V .s2) R) hcb
  exact ⟨co.env, by rw [co.out c0, ← Proof.Gcm.gctr_eq], co.frame⟩

theorem oneCryptWith_ok {o : Bool} {R : Nat} {S D : Addr} {s : State} (he : Env V sp s)
    (h28 : V .s3 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hd : DataW (V .s2) (V .s1) (V .s0) s D (V .s11).toNat) (hs : DataOk (V .s1) (V .s0) s S (V .s11).toNat)
    (ha : Alias o S D (V .s11).toNat)
    (hδ : o = true → V .s9 = D - S)
    (hDs : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = S)
    {icb : Block} (hcb : blockAt s.mem (V .s1 + BitVec.ofNat 64 48) = icb) :
    WP isa (oneCryptWith o) s (OC V sp R icb S D s.mem) :=
  oneCryptB_ok L (bs := false) he h28 hR hd hs ha hδ hDs hcb Bool.noConfusion

/-- `oneCrypt`: in place. -/
theorem oneCrypt_ok {R : Nat} {D : Addr} {s : State} (he : Env V sp s) (h28 : V .s3 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hd : DataW (V .s2) (V .s1) (V .s0) s D (V .s11).toNat)
    (hDs : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    {icb : Block} (hcb : blockAt s.mem (V .s1 + BitVec.ofNat 64 48) = icb) :
    WP isa oneCrypt s (OC V sp R icb D D s.mem) :=
  oneCryptWith_ok L (o := false) he h28 hR hd hd.ok rfl (fun h => Bool.noConfusion h) hDs hcb

end

theorem padded_eq (a c : List Byte) :
    (a ++ zeros (padLen a.length) ++ c) ++ zeros (padLen (a ++ zeros (padLen a.length) ++ c).length) = padded a c := by
  by_cases hc : c = []
  · subst hc
    have h0 : padLen (a ++ zeros (padLen a.length) ++ []).length = 0 := by
      apply Proof.Gcm.padLen_of_mod
      simp only [List.append_nil, List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
    rw [h0]; simp [padded, Proof.Gcm.ghashInput_nil, zeros]
  · simp only [padded, Proof.Gcm.ghashInput_of_ne hc]

/-- The regions `oneTag o` writes. -/
abbrev otFrame (st w : Addr) (o : Nat) (sp : Addr) : List Region :=
  [⟨st, 48⟩, ⟨w + BitVec.ofNat 64 96, 16⟩, ⟨w + BitVec.ofNat 64 o, 16⟩, ⟨w + BitVec.ofNat 64 512, 2048⟩,
    below sp 2048]

theorem abs_otSub {st w sp : Addr} {o : Nat} :
    ∀ r ∈ absFrame st w 16 sp, ∃ r' ∈ otFrame st w o sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem t_otSub {st w sp : Addr} {o : Nat} : ∀ r ∈ tFrame st w 16 sp, ∃ r' ∈ otFrame st w o sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨⟨w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem tag_otSub {st w sp : Addr} {o : Nat} :
    ∀ r ∈ tagFrame st w o sp, ∃ r' ∈ otFrame st w o sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- After `oneTag o`, from `m₀`, for the tag of `a` and the bytes at `data`
(`D`), from the counter block `J`. -/
structure OT (V : Reg → BitVec 64) (sp : Addr) (o R : Nat) (H : Block) (a : List Byte) (J : Block) (D : Addr)
    (m₀ : Mem) (s : State) : Prop where
  env : Env V sp s
  out : bytesAt s.mem (V .s0 + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt m₀ D (V .s11).toNat))))
      [ofBytes (lensBlock a.length (bytesAt m₀ D (V .s11).toNat).length)] ^^^ ciphOf m₀ (V .s2) R J)
  frame : Frame (otFrame (V .s1) (V .s0) o sp) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0))
include L

/-- `oneTag o`, or with the round keys bitsliced (`bs`), from the buffer at `V s7`. -/
theorem oneTagB_ok [VG.Proof.Gcm.RISCV64.GhashLaw] {bs : Bool} {o R : Nat} (ho : o = 0 ∨ o = 112) {H : Block}
    {a : List Byte} {D : Addr} {s : State}
    (he : Env V sp s) (h28 : V .s3 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H) (hl : (V .s10).toNat = a.length)
    (hab : Absorbed s.mem (V .s1 + BitVec.ofNat 64 16) (V .s1 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length)))
    (hd : DataOk (V .s1) (V .s0) s D (V .s11).toNat)
    (hDs : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D) {S' D' : Addr} {n' : Nat}
    (hb : bs = true → BkIn (V .s7) (V .s2) (V .s1) (V .s0) sp R s.mem S' D' n' s) :
    WP isa (oneTagB bs o) s (OT V sp o R H a (blockAt s.mem (V .s1)) D s.mem) := by
  have hk := he.stk'
  have dC : ∀ r ∈ otFrame (V .s1) (V .s0) o sp, (⟨V .s2, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Region.sub_prefix (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by omega_using [ho]))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact hk.c
  have dJ : ∀ r ∈ absFrame (V .s1) (V .s0) 16 sp ++ tFrame (V .s1) (V .s0) 16 sp,
      (⟨V .s1, 16⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · simpa using stb_abs16 L hk (d := 0) (.inl rfl) r hr
    · simpa using stb_t16 L hk (d := 0) (.inl rfl) r hr
  have hx : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  refine WP.seq (WP.mono (dataArgs_ok he L.wal hDs) fun s₁ ⟨a24, a25, a26, g₁, k₁⟩ => ?_)
  have he₁ := he.keep (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide))
    k₁.sp k₁.rd k₁.wr
  have ai : AbsIn V sp 16 H (a ++ zeros (padLen a.length)) D (V .s11).toNat s₁ :=
    ⟨he₁, a24, a25, by rw [a26, hx], hd.of_eq k₁.rd k₁.wr k₁.sp, by rw [k₁.mem]; exact hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr' (absorb_ok L (.inr rfl) ai)) fun s₂ ⟨ab, rd₂, wr₂⟩ => ?_)
  rw [k₁.mem] at ab
  have h23 := ab.env.fr .s11 (by decide)
  have hand := and15 (V .s11)
  have h₃ : WP isa (.block [.logicImm .and .s6 .s11 15]) s₂ fun s₃ =>
      s₃.gpr .s6 = BitVec.ofNat 64 ((V .s11).toNat % 16) ∧
        (∀ r, r ≠ .s6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    crun [Int.reduceNatCast', h23, hand]
    exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₃ fun s₃ ⟨a26', g₃, k₃⟩ => ?_)
  have he₃ := ab.env.keep (fun r hr => g₃ r (by revert r; decide)) k₃.sp k₃.rd k₃.wr
  have hH₂ : blockAt s₂.mem (V .s2 + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl) hk)]; exact hH
  let ct := bytesAt s.mem D (V .s11).toNat
  have hlx : ((a ++ zeros (padLen a.length)) ++ ct).length % 16 = (V .s11).toNat % 16 := by
    simp only [List.length_append, Proof.Gcm.length_zeros, ct, length_bytesAt] at hx ⊢; omega_using [hx]
  refine WP.seq (WP.mono (WP.with_rdwr' (flush_ok L (yo := 16) (.inr rfl) (x := (a ++ zeros (padLen a.length)) ++ ct)
    (H := H) ⟨he₃, by rw [k₃.mem]; exact hH₂⟩ (by rw [a26', hlx]))) fun s₄ ⟨fl, rd₄, wr₄⟩ => ?_)
  rw [k₃.mem] at fl
  have e22 := fl.env.fr .s10 (by decide)
  have e23 := fl.env.fr .s11 (by decide)
  have h₅ : WP isa (.block [mov .s4 .s10, mov .s6 .s11]) s₄ fun s₅ =>
      s₅.gpr .s4 = V .s10 ∧ s₅.gpr .s6 = V .s11 ∧ (∀ r, r ≠ .s4 → r ≠ .s6 → s₅.gpr r = s₄.gpr r) ∧
        Keeps s₄ s₅ := by
    crun [Int.reduceNatCast', mov, e22, e23]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₅ fun s₅ ⟨h24₅, h26₅, g₅, k₅⟩ => ?_)
  have he₅ := fl.env.keep (fun r hr => g₅ r (by revert r; decide) (by revert r; decide)) k₅.sp k₅.rd k₅.wr
  have f₄ : Frame (absFrame (V .s1) (V .s0) 16 sp ++ tFrame (V .s1) (V .s0) 16 sp) s.mem s₄.mem :=
    (ab.frame.mono (fun r hr => List.mem_append_left _ hr)).trans
      (fl.frame.mono (fun r hr => List.mem_append_right _ hr))
  have hj : ∀ r ∈ absFrame (V .s1) (V .s0) 16 sp ++ tFrame (V .s1) (V .s0) 16 sp,
      ∃ r' ∈ j0Frame (V .s1) (V .s0) sp, Region.Sub r r' := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact abs16_j0 r hr
    · exact t16_j0 r hr
  refine WP.mono (tagB_ok L (bs := bs) ho he₅ h28 hR (H := H) (by rw [k₅.mem]; exact fl.hH) rfl
    (S := S') (D := D') (n := n') fun hbs => ?_) fun s₆ tg => ?_
  · obtain hb₀ := hb hbs
    rw [k₅.mem]
    refine hb₀.frame hR f₄ (fun r hr => ?_) (fun r hr => ?_)
      (by rw [k₅.rd, rd₄, k₃.rd, rd₂, k₁.rd]) (by rw [k₅.wr, wr₄, k₃.wr, wr₂, k₁.wr])
    · obtain ⟨r', hr', hs⟩ := hj r hr; exact (hb₀.j0Frame r' hr').sub_right hs
    · obtain ⟨r', hr', hs⟩ := hj r hr; exact (ctx_j0Frame L hk r' hr').sub_right hs
  rw [h24₅, h26₅, k₅.mem] at tg
  refine ⟨tg.env, ?_, ?_⟩
  · rw [tg.out]
    have hw := (fl.abs (ab.abs hab)).whole_eq (by
      simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
    rw [padded_eq] at hw
    rw [hw, ciph_frame f₄ (fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · obtain ⟨r', hr', hs⟩ := abs_otSub (o := o) r hr; exact (dC r' hr').sub_right hs
        · obtain ⟨r', hr', hs⟩ := t_otSub (o := o) r hr; exact (dC r' hr').sub_right hs) hR,
      blockAt_frame f₄ dJ, hl]
    simp only [ct, length_bytesAt]
  · refine (f₄.sub fun r hr => ?_).trans (tg.frame.sub tag_otSub)
    rcases List.mem_append.mp hr with hr | hr
    · exact abs_otSub r hr
    · exact t_otSub r hr


theorem oneTag_ok [VG.Proof.Gcm.RISCV64.GhashLaw] {o R : Nat} (ho : o = 0 ∨ o = 112) {H : Block} {a : List Byte} {D : Addr} {s : State}
    (he : Env V sp s) (h28 : V .s3 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H) (hl : (V .s10).toNat = a.length)
    (hab : Absorbed s.mem (V .s1 + BitVec.ofNat 64 16) (V .s1 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length)))
    (hd : DataOk (V .s1) (V .s0) s D (V .s11).toNat)
    (hDs : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D) :
    WP isa (oneTag o) s (OT V sp o R H a (blockAt s.mem (V .s1)) D s.mem) :=
  oneTagB_ok L (bs := false) ho he h28 hR hH hl hab hd hDs (S' := 0) (D' := 0) (n' := 0) Bool.noConfusion
end

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTCrypt.lean`): the entry, `oneAad`, `oneCrypt`, `oneTag 0`
and the tag copied out to `tag` (`seal_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ghashInput fullTag zeros padLen j0 inc32 gctr encryptWith toBytes)
open VG.Proof.Gcm (Absorbed)

/-- The state at `W + 16`, inside the working space `W`. -/
theorem oneLay {c W : Addr} (fc : c.toNat + 256 ≤ 2 ^ 64) (fW : W.toNat + 2560 ≤ 2 ^ 64)
    (dcW : (⟨c, 256⟩ : Region).Disjoint ⟨W, 2560⟩) (ca : c.toNat % 8 = 0) (wa : W.toNat % 8 = 0) :
    Lay c (W + BitVec.ofNat 64 16) W := by
  obtain sw : (W + BitVec.ofNat 64 16).toNat + 80 ≤ 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide),
      Nat.mod_eq_of_lt (by omega_using [fW])]
    omega_using [fW]
  obtain sa : (⟨W + BitVec.ofNat 64 16, 80⟩ : Region).Disjoint ⟨W, 16⟩ := by
    simpa using Lay.w_w (w := W) (a := 16) (n := 80) (d := 0) (k := 16) (.inr (by decide)) (by decide)
      (by decide)
  obtain sb : (⟨W + BitVec.ofNat 64 16, 80⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 96, 2464⟩ :=
    Lay.w_w (a := 16) (n := 80) (d := 96) (k := 2464) (.inl (by decide)) (by decide) (by decide)
  exact ⟨fc, sw, fW, dcW.sub_right (Lay.wSub (by decide)), dcW, sa, sb, ca, Spill.al8 wa (by decide), wa⟩

theorem stackArgAddr_0 (s : State) : stackArgAddr s 0 = s.sp + BitVec.ofNat 64 0 := rfl

/-- The stack arguments, in a state that may read them. -/
theorem args_in {s : State} {n : Nat} (h : Covers [args s n] (s.rd ++ s.wr)) (hn : n ≤ 3) {i : Nat}
    (hi : i < n) : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * i)) 8 := by
  have := in_off h (d := 8 * i) (n := 8) (by omega_using [hi]) (by omega_using [hn])
  rwa [stackArgAddr_0, add_ofNat_assoc, Nat.zero_add] at this

/-- The stack below `sp`, for the state at `W + 16`. -/
theorem one_stk {s : State} {rs : List Region} (h : stkOk s rs) {c W : Addr} (hc : ⟨c, 256⟩ ∈ rs)
    (hw : ⟨W, 2560⟩ ∈ rs) : StkOk c (W + BitVec.ofNat 64 16) W s.sp :=
  ⟨h.buf hc, (h.buf hw).sub_left (Lay.wSub (by decide)), h.buf hw, h.1, h.2.1⟩

/-- After the entry, the environment. -/
theorem one_env {s₀ s₁ : State} {W T : Addr} (h1 : SO1 W T s₀ s₁)
    (hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr)) (hW : Covers [⟨W, 2560⟩] s₀.wr)
    (hk : StkOk (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₀.sp) :
    Env s₁.gpr s₀.sp s₁ := by
  obtain perm : Perm (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₁ :=
    (⟨hC, covers_off hW (show 16 + 80 ≤ 2560 by decide) (by decide), hW⟩ :
      Perm (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₀).of_eq h1.keeps.rd h1.keeps.wr
  exact ⟨fun _ _ => rfl, h1.keeps.sp, by rw [h1.s2, h1.s1, h1.s0]; exact perm,
    by rw [h1.s2, h1.s1, h1.s0, h1.keeps.sp]; exact hk⟩

section
variable {c st w : Addr} (L : Lay c st w)
include L

theorem saved_otFrame {sp : Addr} (hk : StkOk c st w sp) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ otFrame st w o sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.saved_st (d := 0) (k := 48) (by decide)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by omega_using [ho]) (.inl (by omega_using [ho]))
  · exact saved_w (by decide) (.inr (by decide))
  · exact saved_below hk

end

theorem seal_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : sealRISCV64.pre s₀) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealRISCV64.post s₀ s' := by
  have h' : sealPre s₀ := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, fW, fsp, hR, hstk,
    ca, wa⟩ := h'
  obtain L₀ := oneLay fc fW dcW ca wa
  obtain hk₀ : StkOk (s₀.gpr .a0) (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₀.sp :=
    one_stk hstk (by simp) (by simp)
  obtain hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hA : Covers [args s₀ 2] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain hTd : (⟨s₀.sp + BitVec.ofNat 64 0, 8⟩ : Region).Disjoint (oneR (stackArg s₀ 1)) :=
    ((dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).sub_right
      (Region.sub_prefix (show 8 ≤ 8 * 2 by decide))).symm
  refine WP.seq (WP.mono (one1_wp (off := 8) (W := stackArg s₀ 1) (T := stackArg s₀ 0) (.inl rfl) hW wa hstk.1
    (args_in hA (by decide) (i := 1) (by decide)) rfl (args_in hA (by decide) (i := 0) (by decide)) rfl hTd)
    fun s₁ h1 => ?_)
  obtain he₁ := one_env h1 hC hW hk₀
  obtain L := L₀.v h1.s2 h1.s1 h1.s0
  have f₁ := h1.frame
  have hk₁ := h1.keeps
  obtain cO : ∀ r ∈ [oneR (stackArg s₀ 1)], (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dcW.sub_right (Lay.wSub (by decide))
  -- `oneAad`
  obtain hH₁ : blockAt s₁.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
    rw [h1.s2]; exact ctxH_keep f₁ cO
  obtain hN : DataOk (s₁.gpr .s1) (s₁.gpr .s0) s₁ (s₀.gpr .a2) (s₀.gpr .a3).toNat := by
    rw [h1.s1, h1.s0]
    exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)), (s₀.gpr .a3).isLt,
      fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  obtain hAd : DataOk (s₁.gpr .s1) (s₁.gpr .s0) s₁ (s₀.gpr .a4) (s₁.gpr .s10).toNat := by
    rw [h1.s1, h1.s0, h1.s10]
    exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)), (s₀.gpr .a5).isLt,
      fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  obtain toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₁ hH₁ h1.s4 (by rw [h1.s5]; exact toN)
    (by rw [h1.s7]; exact toN) hN hAd (by rw [h1.s0]; exact h1.aad))) fun s₂ ⟨oa, rd₂, wr₂, sp₂⟩ => ?_)
  -- `oneCrypt`
  obtain hd₂ : DataW (s₁.gpr .s2) (s₁.gpr .s1) (s₁.gpr .s0) s₂ (s₀.gpr .a6) (s₁.gpr .s11).toNat := by
    rw [h1.s2, h1.s1, h1.s0, h1.s11]
    obtain hDw : Covers [⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩] s₂.wr := by
      rw [wr₂, hk₁.wr, hwr]; exact covers_mem (by simp)
    exact ⟨⟨covers_left hDw, (s₀.gpr .a7).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW,
      by rw [sp₂, hk₁.sp]; exact hstk.buf (by simp)⟩, hDw, dcd⟩
  obtain h28 : s₁.gpr .s3 = BitVec.ofNat 64 (s₀.gpr .a1).toNat := by rw [h1.s3]; exact toN
  obtain hD₂s : s₂.mem.readW (s₁.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6 := by
    rw [slot_keep oa.frame (slot_j0 L he₁.stk' (by decide)), h1.s0]; exact h1.dat
  refine WP.seq (WP.mono (WP.with_rdwr (oneCrypt_ok L oa.env h28 hR hd₂ hD₂s oa.cb))
    fun s₃ ⟨oc, rd₃, wr₃, sp₃⟩ => ?_)
  -- `oneTag 0`
  obtain hH₃ : blockAt s₃.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
    rw [blockAt_frame oc.frame (fun r hr => (ctx_crFrame L hd₂ r hr).sub_left (Lay.ctxSub (by decide)))]
    exact oa.hH
  obtain hb := Nat.mod_lt (bytesAt s₁.mem (s₀.gpr .a4) (s₁.gpr .s10).toNat ++
    zeros (padLen (bytesAt s₁.mem (s₀.gpr .a4) (s₁.gpr .s10).toNat).length)).length (show 16 > 0 by decide)
  obtain hab₃ := oa.abs.congr (blockAt_frame oc.frame (stp_crFrame L hd₂ (by decide)))
    (bytesAt_frame oc.frame (stp_crFrame L hd₂ (by omega_using [])) (by omega_using []))
  obtain hD₃s : s₃.mem.readW (s₁.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6 := by
    rw [slot_keep oc.frame (slot_crFrame L hd₂ (by decide))]; exact hD₂s
  refine WP.seq (WP.mono (WP.with_rdwr (oneTag_ok L (o := 0) (.inl rfl) oc.env h28 hR hH₃
    (length_bytesAt _ _ _).symm hab₃ (hd₂.ok.of_eq rd₃ wr₃ sp₃) hD₃s)) fun s₄ ⟨ot, rd₄, wr₄, _⟩ => ?_)
  -- the tag copied out
  obtain hTw : Covers [⟨s₁.gpr .s9, 16⟩] s₄.wr := by
    rw [wr₄, wr₃, wr₂, hk₁.wr, h1.s9, hwr]; exact covers_mem (by simp)
  obtain hTd' : (⟨s₁.gpr .s9, 16⟩ : Region).Disjoint ⟨s₁.gpr .s0, 16⟩ := by
    rw [h1.s9, h1.s0]; exact dtW.sub_right (Region.sub_prefix (by decide))
  refine WP.seq (WP.mono (tagOut_ok ot.env hTw hTd') fun s₅ ⟨hb₅, hf₅, g₅, k₅⟩ => ?_)
  obtain he₅ := ot.env.keep (fun r hr => g₅ r (by revert r; decide)) k₅.sp k₅.rd k₅.wr
  have of₄ := ot.frame
  rw [h1.s1, h1.s0] at of₄
  have cf₃ := oc.frame
  rw [h1.s1, h1.s0, h1.s11] at cf₃
  have jf₂ := oa.frame
  rw [h1.s1, h1.s0] at jf₂
  obtain hd₂₀ : DataW (s₀.gpr .a0) (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₂ (s₀.gpr .a6)
      (s₀.gpr .a7).toNat := by rw [← h1.s2, ← h1.s1, ← h1.s0, ← h1.s11]; exact hd₂
  have sv₁ : SavedAt s₁.mem (stackArg s₀ 1) s₀ := h1.saved
  obtain sv₅ : SavedAt s₅.mem (stackArg s₀ 1) s₀ :=
    (((sv₁.frame jf₂ (saved_j0Frame L₀ hk₀)).frame cf₃ (saved_crFrame L₀ hd₂₀)).frame of₄
      (saved_otFrame L₀ hk₀ (.inl rfl))).frame (by rw [h1.s9] at hf₅; exact hf₅) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dtW.sub_right (Lay.wSub (by decide))).symm)
  obtain e31 : s₅.gpr .s0 = stackArg s₀ 1 := (he₅.fr _ (by decide)).trans h1.s0
  refine WP.mono (restore_ok e31 wa (by have := he₅.perm.w; rw [h1.s0] at this; exact Covers.right this) sv₅
    he₅.sp) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  -- the results
  obtain f₂ : Frame (oneR (stackArg s₀ 1) :: j0Frame (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₀.sp)
      s₀.mem s₂.mem :=
    (f₁.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..).trans
      (jf₂.mono fun r hr => List.mem_cons_of_mem _ hr)
  obtain dc₂ : ∀ r ∈ oneR (stackArg s₀ 1) :: j0Frame (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₀.sp,
      (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact dcW.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L₀.cs
      · exact dcW.sub_right (Lay.wSub (by decide))
      · exact dcW.sub_right (Lay.wSub (by decide))
      · exact hk₀.c
  obtain dD : ∀ r ∈ oneR (stackArg s₀ 1) :: j0Frame (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₀.sp,
      (⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact data_j0 hd₂₀.ok (sp₂.trans hk₁.sp) r hr
  obtain hc₂ := ciph_keep f₂ dc₂ hR
  obtain hc₃ : ciphOf s₃.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat = ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat := by
    rw [ciph_frame cf₃ (ctx_crFrame L₀ hd₂₀) hR, hc₂]
  obtain hD₂ : bytesAt s₂.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat :=
    bytesAt_frame f₂ dD (by have := (s₀.gpr .a7).isLt; omega_using [])
  obtain hiv : bytesAt s₁.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat = bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnW.sub_right (Lay.wSub (by decide)))
      (by have := (s₀.gpr .a3).isLt; omega_using [])
  obtain haad : bytesAt s₁.mem (s₀.gpr .a4) (s₁.gpr .s10).toNat = bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat := by
    rw [h1.s10]
    exact bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact daW.sub_right (Lay.wSub (by decide)))
      (by have := (s₀.gpr .a5).isLt; omega_using [])
  obtain hj₃ : blockAt s₃.mem (stackArg s₀ 1 + BitVec.ofNat 64 16) =
      j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat) := by
    rw [blockAt_frame cf₃ (by simpa using stp_crFrame L₀ hd₂₀ (d := 0) (k := 16) (by decide)), ← hiv, ← h1.s1]
    exact oa.j
  obtain hD₃ : bytesAt s₃.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat =
      gctr (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
        (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat)))
        (bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat) := by
    have := oc.out
    rw [h1.s11, h1.s2, hc₂, hD₂, hiv] at this
    exact this
  obtain hD₄ : bytesAt s₄.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = bytesAt s₃.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat := by
    refine bytesAt_frame of₄ (fun r hr => ?_) (by have := (s₀.gpr .a7).isLt; omega_using [])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact hstk.buf (by simp)
  obtain hD₅ : bytesAt s₅.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = bytesAt s₄.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat :=
    bytesAt_frame hf₅ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h1.s9]; exact ddt)
      (by have := (s₀.gpr .a7).isLt; omega_using [])
  have ho := ot.out
  rw [h1.s2, h1.s1, h1.s11, h1.s0, hc₃, hj₃, haad, BitVec.add_zero, ← Proof.Gcm.fullTag_eq] at ho
  rw [h1.s0, h1.s9] at hb₅
  simp only [sealRISCV64, encryptWith, hm, hD₅, hD₄, hD₃, hb₅, ho]
  refine Prod.ext rfl ?_
  exact List.take_of_length_le (by rw [Spec.Gcm.fullTag, Proof.Gcm.length_gctr, Proof.Cmac.toBytes_length])

end VG.Proof.AesGcm.RISCV64
