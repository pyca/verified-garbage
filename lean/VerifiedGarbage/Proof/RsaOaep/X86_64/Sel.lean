module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
public import VerifiedGarbage.Spec.HashId
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSAES-OAEP on x86-64: the selectors

`selPrologue` copies the selectors, stack arguments `jH` and `jG`, to
their slots, stores the lengths of the hash functions they name (`selW`,
by a dispatch over `lens`, `chainL_wp`), and copies the words of the tables
the stack arguments `jG + 1` and `jG + 2` point to, the addresses of the
hash functions' streaming functions, to their slots (`fnW`): `selPro_ok`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)
open VG.Proof.Bignum (off word)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Impl.Mgf1.X86_64 (at_)
open VG.Proof.Dispatch.X86_64 (FlagsOnly)

/-- The hash functions' digest lengths: `HashId.mgf1`'s `hLen` of the key,
at most 64. -/
def lenOf (k : Nat) : Nat := ((Spec.HashId.mgf1 k).map (·.len)).getD 0

/-- `lens`' keys are distinct and below `2^31` (`cmp rax, k`), and each
length is the digest length of the hash function `HashId.mgf1` names, at
most 64 bytes. -/
theorem lens_nodup : (lens.map (·.1)).Nodup := by decide
theorem lens_lt : ∀ i ∈ lens.map (·.1), i < 2 ^ 31 := by decide
theorem lens_len : ∀ p ∈ lens, p.2 = lenOf p.1 := by decide
theorem lens_le : ∀ p ∈ lens, p.2 ≤ 64 := by decide

/-- A list of numbers and digest lengths a dispatch chooses among: distinct
keys below `2^31`, lengths at most 64. -/
structure LensOK (ls : List (Nat × Nat)) : Prop where
  nodup : (ls.map (·.1)).Nodup
  lt : ∀ i ∈ ls.map (·.1), i < 2 ^ 31
  le : ∀ p ∈ ls, p.2 ≤ 64

theorem lensOK : LensOK lens := ⟨lens_nodup, lens_lt, lens_le⟩

/-- With distinct keys, one value per key. -/
theorem keys_unique {α : Type} {cs : List (Nat × α)} (hnd : (cs.map (·.1)).Nodup) {k : Nat} {a b : α}
    (h₁ : (k, a) ∈ cs) (h₂ : (k, b) ∈ cs) : a = b := by
  induction cs with
  | nil => cases h₁
  | cons p cs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h₁ with e₁ | e₁ <;> rcases List.mem_cons.mp h₂ with e₂ | e₂
    · rw [← e₁] at e₂; cases e₂; rfl
    · subst e₁; exact absurd (List.mem_map.mpr ⟨_, e₂, rfl⟩) hnd.1
    · subst e₂; exact absurd (List.mem_map.mpr ⟨_, e₁, rfl⟩) hnd.1
    · exact ih hnd.2 e₁ e₂

/-- The dispatch on `rax = k` to `f D` for each `(i, D)` of `ls`: `f D`
for the `(k, D)` of `ls`, from a state that differs only in the flags. -/
theorem chainLW_wp {ls : List (Nat × Nat)} (hls : LensOK ls) {f : Nat → Prog isa} {k D : Nat} (hk : (k, D) ∈ ls) {t : State} {Q : State → Prop}
    (hax : t.gpr .rax = BitVec.ofNat 64 k) (h : ∀ s', FlagsOnly t s' → WP isa (f D) s' Q) :
    WP isa (Impl.Dispatch.X86_64.chain (ls.map fun p => (p.1, f p.2))) t Q := by
  have hkeys : Proof.Dispatch.keys (ls.map fun p => (p.1, f p.2)) = ls.map (·.1) := by
    simp only [Proof.Dispatch.keys, List.map_map]; rfl
  have hkm : k ∈ ls.map (·.1) := List.mem_map.mpr ⟨_, hk, rfl⟩
  have hk31 := hls.lt k hkm
  have hsel : Proof.Dispatch.X86_64.sel t = k := by
    simp only [Proof.Dispatch.X86_64.sel, hax, BitVec.toNat_ofNat]; omega
  refine Proof.Dispatch.chain_wp Proof.Dispatch.X86_64.tests _ (by rw [hkeys]; exact hls.lt)
    (by rw [hkeys, hsel]; exact hkm) (by rw [hkeys]; exact hls.nodup) fun c hc s' hs' _ => ?_
  rw [hsel] at hc
  obtain ⟨⟨i, D'⟩, hm, he⟩ := List.mem_map.mp hc
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [keys_unique hls.nodup hm hk]; exact h s' hs'

theorem chainL_wp {f : Nat → Prog isa} {k D : Nat} (hk : (k, D) ∈ lens) {t : State} {Q : State → Prop}
    (hax : t.gpr .rax = BitVec.ofNat 64 k) (h : ∀ s', FlagsOnly t s' → WP isa (f D) s' Q) :
    WP isa (Impl.Dispatch.X86_64.chain (lens.map fun p => (p.1, f p.2))) t Q :=
  chainLW_wp lensOK hk hax h

/-- The slots `selPrologue` stores to, over `W`: the selectors `kH` and
`kG`, `H`'s length `D` and the three lengths computed from it, and `G`'s
`DG`. -/
def selW (W : Nat → BitVec 64) (kH kG D DG : Nat) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd W 37 (BitVec.ofNat 64 kH)) 39 (BitVec.ofNat 64 D))
    40 (BitVec.ofNat 64 (D + 1))) 41 (BitVec.ofNat 64 (2 * D + 1))) 42 (BitVec.ofNat 64 (2 * D + 2)))
    38 (BitVec.ofNat 64 kG)) 43 (BitVec.ofNat 64 DG)

theorem frame_wF {F : Addr} (hF : F.toNat + frameBytes + 8 ≤ 2 ^ 64) {m m' : Mem}
    (hf : Frame [⟨F, frameBytes⟩] m m') {d : Nat} (hd : d + 8 ≤ frameBytes) (v : BitVec 64) :
    Frame [⟨F, frameBytes⟩] m (m'.writeW (off F d) v) :=
  hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-- A stack argument, read at `off F (frameBytes + 8 + 8 j)`, to the slot `d`. -/
theorem argSlot_ok {u : State} {F : Addr} (hsp : u.gpr .rsp = F) (hsc : Scr u F frameBytes) {j d : Nat}
    {v : BitVec 64} (hin : InRegions (u.rd ++ u.wr) (off F (frameBytes + 8 + 8 * j)) 8)
    (hv : u.mem.readW (off F (frameBytes + 8 + 8 * j)) 64 = v) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block (argSlot j d)) u fun u' => Keep [.rax] u u' ∧ u'.gpr .rax = v ∧
      u'.mem = u.mem.writeW (off F d) v := by
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.gpr .rax = v ∧ u'.mem = u.mem.writeW (off F d) v) ?_ rfl)
    fun u' ⟨⟨a, b⟩, k⟩ => ⟨k, a, b⟩
  xrun [argSlot, arg, ea_sp, hsp, hin, hv, hsc.st (d := d) hd]

theorem zx64 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `consts D`: the four lengths from `hLen = D`. -/
theorem consts_ok {u : State} {F : Addr} (hsp : u.gpr .rsp = F) (hsc : Scr u F frameBytes) {D : Nat}
    (hD : D ≤ 64) :
    WP isa (.block (consts D)) u fun u' => Keep [.rax] u u' ∧
      u'.mem = (((u.mem.writeW (off F sHD) (BitVec.ofNat 64 D)).writeW (off F sH1) (BitVec.ofNat 64 (D + 1))).writeW
        (off F sH2) (BitVec.ofNat 64 (2 * D + 1))).writeW (off F sH3) (BitVec.ofNat 64 (2 * D + 2)) := by
  refine WP.mono (WP.keep [.rax] ?_ rfl) fun u' ⟨a, k⟩ => ⟨k, a⟩
  xrun [consts, im, ea_sp, hsp, hsc.st (d := sHD) (by decide), hsc.st (d := sH1) (by decide),
    hsc.st (d := sH2) (by decide), hsc.st (d := sH3) (by decide), zx64 (show D < 2 ^ 32 by omega),
    zx64 (show D + 1 < 2 ^ 32 by omega), zx64 (show 2 * D + 1 < 2 ^ 32 by omega),
    zx64 (show 2 * D + 2 < 2 ^ 32 by omega)]

/-- MGF1's length `D`. -/
theorem gd_ok {u : State} {F : Addr} (hsp : u.gpr .rsp = F) (hsc : Scr u F frameBytes) {D : Nat}
    (hD : D ≤ 64) :
    WP isa (.block [.mov32 .rax (im D), .store (sp sGD) .rax]) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off F sGD) (BitVec.ofNat 64 D) := by
  refine WP.mono (WP.keep [.rax] ?_ rfl) fun u' ⟨a, k⟩ => ⟨k, a⟩
  xrun [im, ea_sp, hsp, hsc.st (d := sGD) (by decide), zx64 (show D < 2 ^ 32 by omega)]

theorem keep_of_flags {u u' : State} (h : FlagsOnly u u') : Keep [] u u' :=
  ⟨fun r _ => h.gpr r, h.rd, h.wr⟩

/-- The slots of the tables' words over `W`: `H`'s `init`, `update` and
`finalize` (words 45 to 47), then `G`'s (48 to 50). -/
def fnW (W : Nat → BitVec 64) (h₀ h₁ h₂ g₀ g₁ g₂ : BitVec 64) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd W 45 h₀) 46 h₁) 47 h₂) 48 g₀) 49 g₁) 50 g₂

/-- A table, read through the stack argument `j`: the address `p` it holds,
and the three words at `p`, in any memory that differs from `u`'s only in
the frame. -/
structure TabAt (u : State) (F : Addr) (j : Nat) (p : Addr) (w₀ w₁ w₂ : BitVec 64) : Prop where
  arg : InRegions (u.rd ++ u.wr) (off F (frameBytes + 8 + 8 * j)) 8
  hp : ∀ m', Frame [⟨F, frameBytes⟩] u.mem m' → m'.readW (off F (frameBytes + 8 + 8 * j)) 64 = p
  in₀ : InRegions (u.rd ++ u.wr) p 8
  in₁ : InRegions (u.rd ++ u.wr) (off p 8) 8
  in₂ : InRegions (u.rd ++ u.wr) (off p 16) 8
  rd : ∀ m', Frame [⟨F, frameBytes⟩] u.mem m' →
    m'.readW p 64 = w₀ ∧ m'.readW (off p 8) 64 = w₁ ∧ m'.readW (off p 16) 64 = w₂

theorem TabAt.mono {u u' : State} {F : Addr} {j : Nat} {p : Addr} {w₀ w₁ w₂ : BitVec 64}
    (h : TabAt u F j p w₀ w₁ w₂) (hrd : u'.rd = u.rd) (hwr : u'.wr = u.wr)
    (hf : Frame [⟨F, frameBytes⟩] u.mem u'.mem) : TabAt u' F j p w₀ w₁ w₂ where
  arg := by rw [hrd, hwr]; exact h.arg
  hp m' h' := h.hp m' (hf.trans h')
  in₀ := by rw [hrd, hwr]; exact h.in₀
  in₁ := by rw [hrd, hwr]; exact h.in₁
  in₂ := by rw [hrd, hwr]; exact h.in₂
  rd m' h' := h.rd m' (hf.trans h')

/-- What `fnSlots j d` does after it loads the table's address into `rax`. -/
def fnTail (d : Nat) : List Instr :=
  [.mov .r10 (.mem (at_ .rax)), .store (sp d) .r10, .mov .r10 (.mem (at_ .rax 8)), .store (sp (d + 8)) .r10,
    .mov .r10 (.mem (at_ .rax 16)), .store (sp (d + 16)) .r10]

theorem fnSlots_eq (j d : Nat) : fnSlots j d = ([.mov .rax (.mem (arg j))] : List Instr) ++ fnTail d := rfl

/-- The table's address into `rax`. -/
theorem fnHead_ok {u : State} {F : Addr} (hsp : u.gpr .rsp = F) {j : Nat} {p : Addr} {w₀ w₁ w₂ : BitVec 64}
    (T : TabAt u F j p w₀ w₁ w₂) :
    WP isa (.block [.mov .rax (.mem (arg j))]) u fun u' => Keep [.rax] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .rax = p := by
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .rax = p) ?_ rfl)
    fun u' ⟨⟨a, b⟩, k⟩ => ⟨k, a, b⟩
  xrun [arg, ea_sp, hsp, T.arg, T.hp _ (Frame.refl _ _)]

/-- The three words of the table at `rax` to the slots from `d`. -/
theorem fnTail_ok {u : State} {F : Addr} (hsp : u.gpr .rsp = F) (hsc : Scr u F frameBytes)
    (hF : F.toNat + frameBytes + 8 ≤ 2 ^ 64) {j d : Nat} {p : Addr} {w₀ w₁ w₂ : BitVec 64}
    (T : TabAt u F j p w₀ w₁ w₂) (hax : u.gpr .rax = p) (hd : d + 24 ≤ frameBytes) :
    WP isa (.block (fnTail d)) u fun u' => Keep [.r10] u u' ∧
      u'.mem = ((u.mem.writeW (off F d) w₀).writeW (off F (d + 8)) w₁).writeW (off F (d + 16)) w₂ := by
  have f₁ : Frame [⟨F, frameBytes⟩] u.mem (u.mem.writeW (off F d) w₀) :=
    frame_wF hF (Frame.refl _ _) (by omega) _
  have f₂ := frame_wF hF f₁ (d := d + 8) (by omega) w₁
  have r₀ := (T.rd _ (Frame.refl _ _)).1
  have r₁ := (T.rd _ f₁).2.1
  have r₂ := (T.rd _ f₂).2.2
  refine WP.mono (WP.keep [.r10] (Q := fun u' => u'.mem =
    ((u.mem.writeW (off F d) w₀).writeW (off F (d + 8)) w₁).writeW (off F (d + 16)) w₂) ?_ rfl)
    fun u' ⟨a, k⟩ => ⟨k, a⟩
  xrun [fnTail, ea_sp, ea_at, ea_at0, hsp, hax, T.in₀, T.in₁, T.in₂, r₀, r₁, r₂,
    hsc.st (d := d) (by omega), hsc.st (d := d + 8) (by omega), hsc.st (d := d + 16) (by omega)]

/-- `fnSlots j d`: the three words of the table at the stack argument `j`
to the slots from `d`. -/
theorem fnSlots_ok {u : State} {F : Addr} (hsp : u.gpr .rsp = F) (hsc : Scr u F frameBytes)
    (hF : F.toNat + frameBytes + 8 ≤ 2 ^ 64) {j d : Nat} {p : Addr} {w₀ w₁ w₂ : BitVec 64}
    (T : TabAt u F j p w₀ w₁ w₂) (hd : d + 24 ≤ frameBytes) :
    WP isa (.block (fnSlots j d)) u fun u' => Keep [.rax, .r10] u u' ∧
      u'.mem = ((u.mem.writeW (off F d) w₀).writeW (off F (d + 8)) w₁).writeW (off F (d + 16)) w₂ := by
  rw [fnSlots_eq, WP.block_append_iff]
  refine WP.mono (fnHead_ok hsp T) fun u₁ ⟨k₁, m₁, ax⟩ => ?_
  refine WP.mono (fnTail_ok ((k₁.gpr (by decide)).trans hsp) (hsc.congr k₁.2.2) hF
    (T.mono k₁.2.1 k₁.2.2 (by rw [m₁]; exact Frame.refl _ _)) ax hd) fun u' ⟨k₂, m₂⟩ =>
      ⟨(k₁.trans k₂).mono (by decide), by rw [m₂, m₁]⟩

/-- `selPrologueWith ls`: the selectors to their slots, the lengths of the
hash functions they name, `(kH, DH)` and `(kG, DG)` of `ls`, and the tables'
words. -/
theorem selProW_ok {ls : List (Nat × Nat)} (hls : LensOK ls) {kH kG DH DG : Nat} (hkH : (kH, DH) ∈ ls)
    (hkG : (kG, DG) ∈ ls)
    {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W)
    {jH jG : Nat} (hinH : InRegions (u.rd ++ u.wr) (off F (frameBytes + 8 + 8 * jH)) 8)
    (hinG : InRegions (u.rd ++ u.wr) (off F (frameBytes + 8 + 8 * jG)) 8)
    (harg : ∀ m', Frame [⟨F, frameBytes⟩] u.mem m' →
      m'.readW (off F (frameBytes + 8 + 8 * jH)) 64 = BitVec.ofNat 64 kH ∧
        m'.readW (off F (frameBytes + 8 + 8 * jG)) 64 = BitVec.ofNat 64 kG)
    {pH pG : Addr} {h₀ h₁ h₂ g₀ g₁ g₂ : BitVec 64} (tH : TabAt u F (jG + 1) pH h₀ h₁ h₂)
    (tG : TabAt u F (jG + 2) pG g₀ g₁ g₂) :
    WP isa (selPrologueWith ls jH jG) u fun u' => Lay u' F S ∧ Keep [.rax, .r10] u u' ∧
      Rep u'.mem F S V (fnW (selW W kH kG DH DG) h₀ h₁ h₂ g₀ g₁ g₂) ∧
      Frame [⟨F, frameBytes⟩] u.mem u'.mem := by
  have G' := L.geo
  have hF := L.Fw
  have hsc := L.frScr
  have hDH := hls.le _ hkH
  have hDG := hls.le _ hkG
  -- `Scr` and the stack pointer, for a state keeping the registers and regions of `u`
  have scK : ∀ {rs} {t : State}, Keep rs u t → .rsp ∉ rs → t.gpr .rsp = F ∧ Scr t F frameBytes :=
    fun k hr => ⟨(k.gpr hr).trans L.rsp, Scr.of_mem (k.2.2 ▸ L.fr) (by omega)⟩
  refine WP.seq (WP.mono (argSlot_ok L.rsp hsc hinH (harg _ (Frame.refl _ _)).1 (d := sSelH) (by decide))
    fun u1 ⟨k1, ax1, m1⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (u2 : State) => Lay u2 F S ∧ Keep [.rax] u u2 ∧
      u2.mem = ((((u.mem.writeW (off F sSelH) (BitVec.ofNat 64 kH)).writeW (off F sHD) (BitVec.ofNat 64 DH)).writeW
        (off F sH1) (BitVec.ofNat 64 (DH + 1))).writeW (off F sH2) (BitVec.ofNat 64 (2 * DH + 1))).writeW
        (off F sH3) (BitVec.ofNat 64 (2 * DH + 2))) ?_ fun u2 ⟨L2, k2, m2⟩ => ?_)
  · refine chainLW_wp hls (f := fun D => .block (consts D)) hkH ax1 fun s' hs' => ?_
    have k' := (k1.trans (keep_of_flags hs')).mono (rs' := [.rax]) (by decide)
    obtain ⟨sp', sc'⟩ := scK k' (by decide)
    refine WP.mono (consts_ok sp' sc' hDH) fun u2 ⟨k2, m2⟩ => ?_
    have k12 := (k'.trans k2).mono (rs' := [.rax]) (by decide)
    have R2 : Rep u2.mem F S V (upd (upd (upd (upd (upd W 37 (BitVec.ofNat 64 kH)) 39 (BitVec.ofNat 64 DH))
        40 (BitVec.ofNat 64 (DH + 1))) 41 (BitVec.ofNat 64 (2 * DH + 1))) 42 (BitVec.ofNat 64 (2 * DH + 2))) := by
      rw [m2, hs'.mem, m1]
      exact ((((R.wf G' (k := 37) (by decide) (BitVec.ofNat 64 kH)).wf G' (k := 39) (by decide) _).wf G'
        (k := 40) (by decide) _).wf G' (k := 41) (by decide) _).wf G' (k := 42) (by decide) _
    exact ⟨L.of_rep' R R2 (by simp [upd]) (k12.gpr (by decide)) k12.2.2, k12, by rw [m2, hs'.mem, m1]⟩
  have f2 : Frame [⟨F, frameBytes⟩] u.mem u2.mem := by
    rw [m2]
    exact frame_wF hF (frame_wF hF (frame_wF hF (frame_wF hF (frame_wF hF (Frame.refl _ _) (by decide) _)
      (by decide) _) (by decide) _) (by decide) _) (by decide) _
  have hinG2 : InRegions (u2.rd ++ u2.wr) (off F (frameBytes + 8 + 8 * jG)) 8 := by
    rw [k2.2.1, k2.2.2]; exact hinG
  refine WP.seq (WP.mono (argSlot_ok L2.rsp L2.frScr hinG2 (harg _ f2).2 (d := sSelG) (by decide))
    fun u3 ⟨k3, ax3, m3⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (u4 : State) => Lay u4 F S ∧ Keep [.rax] u u4 ∧
      Rep u4.mem F S V (selW W kH kG DH DG) ∧ Frame [⟨F, frameBytes⟩] u.mem u4.mem)
    (chainLW_wp hls (f := fun D => .block [.mov32 .rax (im D), .store (sp sGD) .rax]) hkG ax3 fun s' hs' => ?_)
    fun u4 ⟨L4, k4, R4, f4⟩ => ?_)
  · have k' := (k3.trans (keep_of_flags hs')).mono (rs' := [.rax]) (by decide)
    have k13 := (k2.trans k').mono (rs' := [.rax]) (by decide)
    obtain ⟨sp', sc'⟩ := scK k13 (by decide)
    refine WP.mono (gd_ok sp' sc' hDG) fun u4 ⟨k4, m4⟩ => ?_
    have k14 := (k13.trans k4).mono (rs' := [.rax]) (by decide)
    have R4 : Rep u4.mem F S V (selW W kH kG DH DG) := by
      rw [m4, hs'.mem, m3, m2]
      exact ((((((R.wf G' (k := 37) (by decide) (BitVec.ofNat 64 kH)).wf G' (k := 39) (by decide) _).wf G'
        (k := 40) (by decide) _).wf G' (k := 41) (by decide) _).wf G' (k := 42) (by decide) _).wf G' (k := 38)
        (by decide) _).wf G' (k := 43) (by decide) _
    refine ⟨L.of_rep' R R4 (by simp [selW, upd]) ((k14.gpr (by decide)).trans rfl) k14.2.2, k14, R4, ?_⟩
    rw [m4, hs'.mem, m3]
    exact frame_wF hF (frame_wF hF f2 (by decide) _) (by decide) _
  -- The tables' words.
  show WP isa (.block (fnSlots (jG + 1) sFnH ++ fnSlots (jG + 2) sFnG)) u4 _
  rw [WP.block_append_iff]
  have tH4 := tH.mono k4.2.1 k4.2.2 f4
  refine WP.mono (fnSlots_ok L4.rsp L4.frScr hF tH4 (d := sFnH) (by decide)) fun u5 ⟨k5, m5⟩ => ?_
  have k45 := (k4.trans k5).mono (rs' := [.rax, .r10]) (by decide)
  have f5 : Frame [⟨F, frameBytes⟩] u.mem u5.mem := by
    rw [m5]
    exact frame_wF hF (frame_wF hF (frame_wF hF f4 (by decide) _) (by decide) _) (by decide) _
  have sp5 : u5.gpr .rsp = F := (k45.gpr (by decide)).trans L.rsp
  have sc5 : Scr u5 F frameBytes := Scr.of_mem (k45.2.2 ▸ L.fr) (by omega)
  have tG5 := tG.mono k45.2.1 k45.2.2 f5
  refine WP.mono (fnSlots_ok sp5 sc5 hF tG5 (d := sFnG) (by decide)) fun u6 ⟨k6, m6⟩ => ?_
  have k16 := (k45.trans k6).mono (rs' := [.rax, .r10]) (by decide)
  have R6 : Rep u6.mem F S V (fnW (selW W kH kG DH DG) h₀ h₁ h₂ g₀ g₁ g₂) := by
    rw [m6, m5]
    exact (((((R4.wf G' (k := 45) (by decide) h₀).wf G' (k := 46) (by decide) h₁).wf G' (k := 47) (by decide)
      h₂).wf G' (k := 48) (by decide) g₀).wf G' (k := 49) (by decide) g₁).wf G' (k := 50) (by decide) g₂
  refine ⟨L.of_rep' R R6 (by simp [fnW, selW, upd]) ((k16.gpr (by decide)).trans rfl) k16.2.2, k16, R6, ?_⟩
  rw [m6]
  exact frame_wF hF (frame_wF hF (frame_wF hF f5 (by decide) _) (by decide) _) (by decide) _

/-- `selPrologue`, over `lens`. -/
theorem selPro_ok {kH kG DH DG : Nat} (hkH : (kH, DH) ∈ lens) (hkG : (kG, DG) ∈ lens)
    {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W)
    {jH jG : Nat} (hinH : InRegions (u.rd ++ u.wr) (off F (frameBytes + 8 + 8 * jH)) 8)
    (hinG : InRegions (u.rd ++ u.wr) (off F (frameBytes + 8 + 8 * jG)) 8)
    (harg : ∀ m', Frame [⟨F, frameBytes⟩] u.mem m' →
      m'.readW (off F (frameBytes + 8 + 8 * jH)) 64 = BitVec.ofNat 64 kH ∧
        m'.readW (off F (frameBytes + 8 + 8 * jG)) 64 = BitVec.ofNat 64 kG)
    {pH pG : Addr} {h₀ h₁ h₂ g₀ g₁ g₂ : BitVec 64} (tH : TabAt u F (jG + 1) pH h₀ h₁ h₂)
    (tG : TabAt u F (jG + 2) pG g₀ g₁ g₂) :
    WP isa (selPrologue jH jG) u fun u' => Lay u' F S ∧ Keep [.rax, .r10] u u' ∧
      Rep u'.mem F S V (fnW (selW W kH kG DH DG) h₀ h₁ h₂ g₀ g₁ g₂) ∧
      Frame [⟨F, frameBytes⟩] u.mem u'.mem :=
  selProW_ok lensOK hkH hkG L R hinH hinG harg tH tG

end VG.Proof.RsaOaep.X86_64
