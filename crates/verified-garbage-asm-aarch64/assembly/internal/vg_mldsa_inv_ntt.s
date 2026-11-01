// The functions of `src/internal/vg_mldsa_inv_ntt.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_inv_ntt:
	movz w9, #57857, lsl #0
	movk w9, #63, lsl #16
	str w9, [x1, #0]
	movz w9, #31498, lsl #0
	movk w9, #127, lsl #16
	str w9, [x1, #4]
	movz w9, #52990, lsl #0
	movk w9, #39, lsl #16
	str w9, [x1, #8]
	movz w9, #60157, lsl #0
	movk w9, #7, lsl #16
	str w9, [x1, #12]
	movz w9, #16829, lsl #0
	movk w9, #124, lsl #16
	str w9, [x1, #16]
	movz w9, #57064, lsl #0
	movk w9, #11, lsl #16
	str w9, [x1, #20]
	movz w9, #24280, lsl #0
	movk w9, #13, lsl #16
	str w9, [x1, #24]
	movz w9, #49629, lsl #0
	movk w9, #120, lsl #16
	str w9, [x1, #28]
	movz w9, #470, lsl #0
	movk w9, #100, lsl #16
	str w9, [x1, #32]
	movz w9, #63190, lsl #0
	movk w9, #91, lsl #16
	str w9, [x1, #36]
	movz w9, #31571, lsl #0
	movk w9, #5, lsl #16
	str w9, [x1, #40]
	movz w9, #60289, lsl #0
	movk w9, #31, lsl #16
	str w9, [x1, #44]
	movz w9, #17804, lsl #0
	movk w9, #80, lsl #16
	str w9, [x1, #48]
	movz w9, #1271, lsl #0
	movk w9, #44, lsl #16
	str w9, [x1, #52]
	movz w9, #26040, lsl #0
	movk w9, #80, lsl #16
	str w9, [x1, #56]
	movz w9, #64218, lsl #0
	movk w9, #86, lsl #16
	str w9, [x1, #60]
	movz w9, #18857, lsl #0
	movk w9, #86, lsl #16
	str w9, [x1, #64]
	movz w9, #16273, lsl #0
	movk w9, #112, lsl #16
	str w9, [x1, #68]
	movz w9, #31324, lsl #0
	movk w9, #16, lsl #16
	str w9, [x1, #72]
	movz w9, #10361, lsl #0
	movk w9, #73, lsl #16
	str w9, [x1, #76]
	movz w9, #25200, lsl #0
	movk w9, #8, lsl #16
	str w9, [x1, #80]
	movz w9, #5472, lsl #0
	movk w9, #17, lsl #16
	str w9, [x1, #84]
	movz w9, #59033, lsl #0
	movk w9, #87, lsl #16
	str w9, [x1, #88]
	movz w9, #11397, lsl #0
	movk w9, #32, lsl #16
	str w9, [x1, #92]
	movz w9, #21034, lsl #0
	movk w9, #32, lsl #16
	str w9, [x1, #96]
	movz w9, #58649, lsl #0
	movk w9, #58, lsl #16
	str w9, [x1, #100]
	movz w9, #23305, lsl #0
	movk w9, #21, lsl #16
	str w9, [x1, #104]
	movz w9, #872, lsl #0
	movk w9, #50, lsl #16
	str w9, [x1, #108]
	movz w9, #4044, lsl #0
	movk w9, #101, lsl #16
	str w9, [x1, #112]
	movz w9, #19422, lsl #0
	movk w9, #0, lsl #16
	str w9, [x1, #116]
	movz w9, #44544, lsl #0
	movk w9, #66, lsl #16
	str w9, [x1, #120]
	movz w9, #39484, lsl #0
	movk w9, #123, lsl #16
	str w9, [x1, #124]
	movz w9, #38298, lsl #0
	movk w9, #86, lsl #16
	str w9, [x1, #128]
	movz w9, #27105, lsl #0
	movk w9, #126, lsl #16
	str w9, [x1, #132]
	movz w9, #60212, lsl #0
	movk w9, #80, lsl #16
	str w9, [x1, #136]
	movz w9, #316, lsl #0
	movk w9, #74, lsl #16
	str w9, [x1, #140]
	movz w9, #23293, lsl #0
	movk w9, #25, lsl #16
	str w9, [x1, #144]
	movz w9, #53204, lsl #0
	movk w9, #54, lsl #16
	str w9, [x1, #148]
	movz w9, #47148, lsl #0
	movk w9, #38, lsl #16
	str w9, [x1, #152]
	movz w9, #8530, lsl #0
	movk w9, #68, lsl #16
	str w9, [x1, #156]
	movz w9, #60027, lsl #0
	movk w9, #58, lsl #16
	str w9, [x1, #160]
	movz w9, #29060, lsl #0
	movk w9, #46, lsl #16
	str w9, [x1, #164]
	movz w9, #21867, lsl #0
	movk w9, #73, lsl #16
	str w9, [x1, #168]
	movz w9, #49599, lsl #0
	movk w9, #43, lsl #16
	str w9, [x1, #172]
	movz w9, #56321, lsl #0
	movk w9, #73, lsl #16
	str w9, [x1, #176]
	movz w9, #38323, lsl #0
	movk w9, #4, lsl #16
	str w9, [x1, #180]
	movz w9, #2405, lsl #0
	movk w9, #92, lsl #16
	str w9, [x1, #184]
	movz w9, #15011, lsl #0
	movk w9, #8, lsl #16
	str w9, [x1, #188]
	movz w9, #60867, lsl #0
	movk w9, #25, lsl #16
	str w9, [x1, #192]
	movz w9, #5418, lsl #0
	movk w9, #25, lsl #16
	str w9, [x1, #196]
	movz w9, #25059, lsl #0
	movk w9, #74, lsl #16
	str w9, [x1, #200]
	movz w9, #20647, lsl #0
	movk w9, #58, lsl #16
	str w9, [x1, #204]
	movz w9, #23490, lsl #0
	movk w9, #74, lsl #16
	str w9, [x1, #208]
	movz w9, #43497, lsl #0
	movk w9, #32, lsl #16
	str w9, [x1, #212]
	movz w9, #27556, lsl #0
	movk w9, #24, lsl #16
	str w9, [x1, #216]
	movz w9, #27765, lsl #0
	movk w9, #71, lsl #16
	str w9, [x1, #220]
	movz w9, #31833, lsl #0
	movk w9, #115, lsl #16
	str w9, [x1, #224]
	movz w9, #50279, lsl #0
	movk w9, #119, lsl #16
	str w9, [x1, #228]
	movz w9, #20619, lsl #0
	movk w9, #113, lsl #16
	str w9, [x1, #232]
	movz w9, #42926, lsl #0
	movk w9, #68, lsl #16
	str w9, [x1, #236]
	movz w9, #23245, lsl #0
	movk w9, #68, lsl #16
	str w9, [x1, #240]
	movz w9, #976, lsl #0
	movk w9, #39, lsl #16
	str w9, [x1, #244]
	movz w9, #17069, lsl #0
	movk w9, #96, lsl #16
	str w9, [x1, #248]
	movz w9, #45267, lsl #0
	movk w9, #42, lsl #16
	str w9, [x1, #252]
	movz w9, #63771, lsl #0
	movk w9, #59, lsl #16
	str w9, [x1, #256]
	movz w9, #21375, lsl #0
	movk w9, #23, lsl #16
	str w9, [x1, #260]
	movz w9, #7729, lsl #0
	movk w9, #56, lsl #16
	str w9, [x1, #264]
	movz w9, #26599, lsl #0
	movk w9, #46, lsl #16
	str w9, [x1, #268]
	movz w9, #10659, lsl #0
	movk w9, #22, lsl #16
	str w9, [x1, #272]
	movz w9, #54803, lsl #0
	movk w9, #74, lsl #16
	str w9, [x1, #276]
	movz w9, #43578, lsl #0
	movk w9, #94, lsl #16
	str w9, [x1, #280]
	movz w9, #12357, lsl #0
	movk w9, #24, lsl #16
	str w9, [x1, #284]
	movz w9, #12427, lsl #0
	movk w9, #19, lsl #16
	str w9, [x1, #288]
	movz w9, #18575, lsl #0
	movk w9, #98, lsl #16
	str w9, [x1, #292]
	movz w9, #20366, lsl #0
	movk w9, #62, lsl #16
	str w9, [x1, #296]
	movz w9, #17162, lsl #0
	movk w9, #15, lsl #16
	str w9, [x1, #300]
	movz w9, #44416, lsl #0
	movk w9, #48, lsl #16
	str w9, [x1, #304]
	movz w9, #11602, lsl #0
	movk w9, #48, lsl #16
	str w9, [x1, #308]
	movz w9, #28448, lsl #0
	movk w9, #55, lsl #16
	str w9, [x1, #312]
	movz w9, #61495, lsl #0
	movk w9, #125, lsl #16
	str w9, [x1, #316]
	movz w9, #53007, lsl #0
	movk w9, #75, lsl #16
	str w9, [x1, #320]
	movz w9, #379, lsl #0
	movk w9, #15, lsl #16
	str w9, [x1, #324]
	movz w9, #6601, lsl #0
	movk w9, #95, lsl #16
	str w9, [x1, #328]
	movz w9, #29026, lsl #0
	movk w9, #86, lsl #16
	str w9, [x1, #332]
	movz w9, #18525, lsl #0
	movk w9, #45, lsl #16
	str w9, [x1, #336]
	movz w9, #23477, lsl #0
	movk w9, #56, lsl #16
	str w9, [x1, #340]
	movz w9, #17811, lsl #0
	movk w9, #6, lsl #16
	str w9, [x1, #344]
	movz w9, #52215, lsl #0
	movk w9, #37, lsl #16
	str w9, [x1, #348]
	movz w9, #15742, lsl #0
	movk w9, #10, lsl #16
	str w9, [x1, #352]
	movz w9, #48877, lsl #0
	movk w9, #18, lsl #16
	str w9, [x1, #356]
	movz w9, #22981, lsl #0
	movk w9, #0, lsl #16
	str w9, [x1, #360]
	movz w9, #62985, lsl #0
	movk w9, #19, lsl #16
	str w9, [x1, #364]
	movz w9, #54307, lsl #0
	movk w9, #5, lsl #16
	str w9, [x1, #368]
	movz w9, #18989, lsl #0
	movk w9, #107, lsl #16
	str w9, [x1, #372]
	movz w9, #39582, lsl #0
	movk w9, #99, lsl #16
	str w9, [x1, #376]
	movz w9, #54174, lsl #0
	movk w9, #21, lsl #16
	str w9, [x1, #380]
	movz w9, #1047, lsl #0
	movk w9, #51, lsl #16
	str w9, [x1, #384]
	movz w9, #54545, lsl #0
	movk w9, #123, lsl #16
	str w9, [x1, #388]
	movz w9, #7146, lsl #0
	movk w9, #120, lsl #16
	str w9, [x1, #392]
	movz w9, #39545, lsl #0
	movk w9, #80, lsl #16
	str w9, [x1, #396]
	movz w9, #13057, lsl #0
	movk w9, #127, lsl #16
	str w9, [x1, #400]
	movz w9, #51522, lsl #0
	movk w9, #16, lsl #16
	str w9, [x1, #404]
	movz w9, #4797, lsl #0
	movk w9, #114, lsl #16
	str w9, [x1, #408]
	movz w9, #30887, lsl #0
	movk w9, #67, lsl #16
	str w9, [x1, #412]
	movz w9, #54326, lsl #0
	movk w9, #56, lsl #16
	str w9, [x1, #416]
	movz w9, #8578, lsl #0
	movk w9, #0, lsl #16
	str w9, [x1, #420]
	movz w9, #42681, lsl #0
	movk w9, #102, lsl #16
	str w9, [x1, #424]
	movz w9, #38464, lsl #0
	movk w9, #49, lsl #16
	str w9, [x1, #428]
	movz w9, #27285, lsl #0
	movk w9, #91, lsl #16
	str w9, [x1, #432]
	movz w9, #14369, lsl #0
	movk w9, #3, lsl #16
	str w9, [x1, #436]
	movz w9, #18272, lsl #0
	movk w9, #116, lsl #16
	str w9, [x1, #440]
	movz w9, #6136, lsl #0
	movk w9, #20, lsl #16
	str w9, [x1, #444]
	movz w9, #64405, lsl #0
	movk w9, #124, lsl #16
	str w9, [x1, #448]
	movz w9, #14328, lsl #0
	movk w9, #54, lsl #16
	str w9, [x1, #452]
	movz w9, #43327, lsl #0
	movk w9, #79, lsl #16
	str w9, [x1, #456]
	movz w9, #16394, lsl #0
	movk w9, #28, lsl #16
	str w9, [x1, #460]
	movz w9, #50029, lsl #0
	movk w9, #36, lsl #16
	str w9, [x1, #464]
	movz w9, #46368, lsl #0
	movk w9, #2, lsl #16
	str w9, [x1, #468]
	movz w9, #52476, lsl #0
	movk w9, #107, lsl #16
	str w9, [x1, #472]
	movz w9, #26735, lsl #0
	movk w9, #107, lsl #16
	str w9, [x1, #476]
	movz w9, #16860, lsl #0
	movk w9, #108, lsl #16
	str w9, [x1, #480]
	movz w9, #12064, lsl #0
	movk w9, #24, lsl #16
	str w9, [x1, #484]
	movz w9, #26300, lsl #0
	movk w9, #12, lsl #16
	str w9, [x1, #488]
	movz w9, #63486, lsl #0
	movk w9, #21, lsl #16
	str w9, [x1, #492]
	movz w9, #4446, lsl #0
	movk w9, #46, lsl #16
	str w9, [x1, #496]
	movz w9, #14436, lsl #0
	movk w9, #59, lsl #16
	str w9, [x1, #500]
	movz w9, #24489, lsl #0
	movk w9, #55, lsl #16
	str w9, [x1, #504]
	movz w9, #18472, lsl #0
	movk w9, #69, lsl #16
	str w9, [x1, #508]
	movz w9, #62830, lsl #0
	movk w9, #95, lsl #16
	str w9, [x1, #512]
	movz w9, #57511, lsl #0
	movk w9, #75, lsl #16
	str w9, [x1, #516]
	movz w9, #34605, lsl #0
	movk w9, #92, lsl #16
	str w9, [x1, #520]
	movz w9, #40457, lsl #0
	movk w9, #69, lsl #16
	str w9, [x1, #524]
	movz w9, #142, lsl #0
	movk w9, #51, lsl #16
	str w9, [x1, #528]
	movz w9, #41478, lsl #0
	movk w9, #93, lsl #16
	str w9, [x1, #532]
	movz w9, #21601, lsl #0
	movk w9, #37, lsl #16
	str w9, [x1, #536]
	movz w9, #23518, lsl #0
	movk w9, #54, lsl #16
	str w9, [x1, #540]
	movz w9, #52492, lsl #0
	movk w9, #123, lsl #16
	str w9, [x1, #544]
	movz w9, #47738, lsl #0
	movk w9, #90, lsl #16
	str w9, [x1, #548]
	movz w9, #56080, lsl #0
	movk w9, #18, lsl #16
	str w9, [x1, #552]
	movz w9, #17572, lsl #0
	movk w9, #74, lsl #16
	str w9, [x1, #556]
	movz w9, #46944, lsl #0
	movk w9, #53, lsl #16
	str w9, [x1, #560]
	movz w9, #23812, lsl #0
	movk w9, #57, lsl #16
	str w9, [x1, #564]
	movz w9, #17578, lsl #0
	movk w9, #18, lsl #16
	str w9, [x1, #568]
	movz w9, #47650, lsl #0
	movk w9, #48, lsl #16
	str w9, [x1, #572]
	movz w9, #8611, lsl #0
	movk w9, #114, lsl #16
	str w9, [x1, #576]
	movz w9, #33255, lsl #0
	movk w9, #99, lsl #16
	str w9, [x1, #580]
	movz w9, #65307, lsl #0
	movk w9, #113, lsl #16
	str w9, [x1, #584]
	movz w9, #24743, lsl #0
	movk w9, #115, lsl #16
	str w9, [x1, #588]
	movz w9, #20606, lsl #0
	movk w9, #120, lsl #16
	str w9, [x1, #592]
	movz w9, #40310, lsl #0
	movk w9, #24, lsl #16
	str w9, [x1, #596]
	movz w9, #43260, lsl #0
	movk w9, #0, lsl #16
	str w9, [x1, #600]
	movz w9, #63748, lsl #0
	movk w9, #7, lsl #16
	str w9, [x1, #604]
	movz w9, #65503, lsl #0
	movk w9, #9, lsl #16
	str w9, [x1, #608]
	movz w9, #42250, lsl #0
	movk w9, #47, lsl #16
	str w9, [x1, #612]
	movz w9, #57213, lsl #0
	movk w9, #96, lsl #16
	str w9, [x1, #616]
	movz w9, #61563, lsl #0
	movk w9, #78, lsl #16
	str w9, [x1, #620]
	movz w9, #18051, lsl #0
	movk w9, #54, lsl #16
	str w9, [x1, #624]
	movz w9, #810, lsl #0
	movk w9, #8, lsl #16
	str w9, [x1, #628]
	movz w9, #47726, lsl #0
	movk w9, #11, lsl #16
	str w9, [x1, #632]
	movz w9, #56894, lsl #0
	movk w9, #54, lsl #16
	str w9, [x1, #636]
	movz w9, #42728, lsl #0
	movk w9, #122, lsl #16
	str w9, [x1, #640]
	movz w9, #32501, lsl #0
	movk w9, #123, lsl #16
	str w9, [x1, #644]
	movz w9, #12991, lsl #0
	movk w9, #37, lsl #16
	str w9, [x1, #648]
	movz w9, #12262, lsl #0
	movk w9, #65, lsl #16
	str w9, [x1, #652]
	movz w9, #27930, lsl #0
	movk w9, #75, lsl #16
	str w9, [x1, #656]
	movz w9, #65477, lsl #0
	movk w9, #50, lsl #16
	str w9, [x1, #660]
	movz w9, #25402, lsl #0
	movk w9, #101, lsl #16
	str w9, [x1, #664]
	movz w9, #50909, lsl #0
	movk w9, #124, lsl #16
	str w9, [x1, #668]
	movz w9, #33052, lsl #0
	movk w9, #84, lsl #16
	str w9, [x1, #672]
	movz w9, #52840, lsl #0
	movk w9, #86, lsl #16
	str w9, [x1, #676]
	movz w9, #34246, lsl #0
	movk w9, #39, lsl #16
	str w9, [x1, #680]
	movz w9, #37520, lsl #0
	movk w9, #108, lsl #16
	str w9, [x1, #684]
	movz w9, #65253, lsl #0
	movk w9, #65, lsl #16
	str w9, [x1, #688]
	movz w9, #54909, lsl #0
	movk w9, #108, lsl #16
	str w9, [x1, #692]
	movz w9, #61360, lsl #0
	movk w9, #89, lsl #16
	str w9, [x1, #696]
	movz w9, #34235, lsl #0
	movk w9, #103, lsl #16
	str w9, [x1, #700]
	movz w9, #31464, lsl #0
	movk w9, #57, lsl #16
	str w9, [x1, #704]
	movz w9, #52035, lsl #0
	movk w9, #108, lsl #16
	str w9, [x1, #708]
	movz w9, #42864, lsl #0
	movk w9, #87, lsl #16
	str w9, [x1, #712]
	movz w9, #9328, lsl #0
	movk w9, #54, lsl #16
	str w9, [x1, #716]
	movz w9, #44919, lsl #0
	movk w9, #45, lsl #16
	str w9, [x1, #720]
	movz w9, #23234, lsl #0
	movk w9, #99, lsl #16
	str w9, [x1, #724]
	movz w9, #54454, lsl #0
	movk w9, #98, lsl #16
	str w9, [x1, #728]
	movz w9, #2394, lsl #0
	movk w9, #16, lsl #16
	str w9, [x1, #732]
	movz w9, #22338, lsl #0
	movk w9, #20, lsl #16
	str w9, [x1, #736]
	movz w9, #65254, lsl #0
	movk w9, #108, lsl #16
	str w9, [x1, #740]
	movz w9, #41410, lsl #0
	movk w9, #50, lsl #16
	str w9, [x1, #744]
	movz w9, #53969, lsl #0
	movk w9, #21, lsl #16
	str w9, [x1, #748]
	movz w9, #57884, lsl #0
	movk w9, #6, lsl #16
	str w9, [x1, #752]
	movz w9, #55610, lsl #0
	movk w9, #107, lsl #16
	str w9, [x1, #756]
	movz w9, #28030, lsl #0
	movk w9, #77, lsl #16
	str w9, [x1, #760]
	movz w9, #62098, lsl #0
	movk w9, #29, lsl #16
	str w9, [x1, #764]
	movz w9, #34477, lsl #0
	movk w9, #19, lsl #16
	str w9, [x1, #768]
	movz w9, #40808, lsl #0
	movk w9, #98, lsl #16
	str w9, [x1, #772]
	movz w9, #55944, lsl #0
	movk w9, #38, lsl #16
	str w9, [x1, #776]
	movz w9, #64083, lsl #0
	movk w9, #20, lsl #16
	str w9, [x1, #780]
	movz w9, #64508, lsl #0
	movk w9, #104, lsl #16
	str w9, [x1, #784]
	movz w9, #1050, lsl #0
	movk w9, #116, lsl #16
	str w9, [x1, #788]
	movz w9, #49689, lsl #0
	movk w9, #93, lsl #16
	str w9, [x1, #792]
	movz w9, #59186, lsl #0
	movk w9, #75, lsl #16
	str w9, [x1, #796]
	movz w9, #18124, lsl #0
	movk w9, #8, lsl #16
	str w9, [x1, #800]
	movz w9, #13812, lsl #0
	movk w9, #43, lsl #16
	str w9, [x1, #804]
	movz w9, #32776, lsl #0
	movk w9, #25, lsl #16
	str w9, [x1, #808]
	movz w9, #11945, lsl #0
	movk w9, #28, lsl #16
	str w9, [x1, #812]
	movz w9, #28389, lsl #0
	movk w9, #39, lsl #16
	str w9, [x1, #816]
	movz w9, #54254, lsl #0
	movk w9, #56, lsl #16
	str w9, [x1, #820]
	movz w9, #53033, lsl #0
	movk w9, #118, lsl #16
	str w9, [x1, #824]
	movz w9, #41441, lsl #0
	movk w9, #57, lsl #16
	str w9, [x1, #828]
	movz w9, #47528, lsl #0
	movk w9, #30, lsl #16
	str w9, [x1, #832]
	movz w9, #49782, lsl #0
	movk w9, #90, lsl #16
	str w9, [x1, #836]
	movz w9, #27722, lsl #0
	movk w9, #90, lsl #16
	str w9, [x1, #840]
	movz w9, #33649, lsl #0
	movk w9, #2, lsl #16
	str w9, [x1, #844]
	movz w9, #617, lsl #0
	movk w9, #98, lsl #16
	str w9, [x1, #848]
	movz w9, #30569, lsl #0
	movk w9, #76, lsl #16
	str w9, [x1, #852]
	movz w9, #2886, lsl #0
	movk w9, #125, lsl #16
	str w9, [x1, #856]
	movz w9, #27737, lsl #0
	movk w9, #18, lsl #16
	str w9, [x1, #860]
	movz w9, #37698, lsl #0
	movk w9, #48, lsl #16
	str w9, [x1, #864]
	movz w9, #25573, lsl #0
	movk w9, #125, lsl #16
	str w9, [x1, #868]
	movz w9, #13817, lsl #0
	movk w9, #103, lsl #16
	str w9, [x1, #872]
	movz w9, #58000, lsl #0
	movk w9, #81, lsl #16
	str w9, [x1, #876]
	movz w9, #33628, lsl #0
	movk w9, #115, lsl #16
	str w9, [x1, #880]
	movz w9, #43111, lsl #0
	movk w9, #102, lsl #16
	str w9, [x1, #884]
	movz w9, #24217, lsl #0
	movk w9, #56, lsl #16
	str w9, [x1, #888]
	movz w9, #29635, lsl #0
	movk w9, #27, lsl #16
	str w9, [x1, #892]
	movz w9, #24260, lsl #0
	movk w9, #46, lsl #16
	str w9, [x1, #896]
	movz w9, #6856, lsl #0
	movk w9, #74, lsl #16
	str w9, [x1, #900]
	movz w9, #57068, lsl #0
	movk w9, #68, lsl #16
	str w9, [x1, #904]
	movz w9, #49729, lsl #0
	movk w9, #123, lsl #16
	str w9, [x1, #908]
	movz w9, #6922, lsl #0
	movk w9, #94, lsl #16
	str w9, [x1, #912]
	movz w9, #58380, lsl #0
	movk w9, #14, lsl #16
	str w9, [x1, #916]
	movz w9, #43546, lsl #0
	movk w9, #101, lsl #16
	str w9, [x1, #920]
	movz w9, #44019, lsl #0
	movk w9, #120, lsl #16
	str w9, [x1, #924]
	movz w9, #33467, lsl #0
	movk w9, #6, lsl #16
	str w9, [x1, #928]
	movz w9, #37681, lsl #0
	movk w9, #101, lsl #16
	str w9, [x1, #932]
	movz w9, #33618, lsl #0
	movk w9, #27, lsl #16
	str w9, [x1, #936]
	movz w9, #47513, lsl #0
	movk w9, #98, lsl #16
	str w9, [x1, #940]
	movz w9, #29032, lsl #0
	movk w9, #25, lsl #16
	str w9, [x1, #944]
	movz w9, #55757, lsl #0
	movk w9, #16, lsl #16
	str w9, [x1, #948]
	movz w9, #64038, lsl #0
	movk w9, #3, lsl #16
	str w9, [x1, #952]
	movz w9, #32805, lsl #0
	movk w9, #58, lsl #16
	str w9, [x1, #956]
	movz w9, #55452, lsl #0
	movk w9, #44, lsl #16
	str w9, [x1, #960]
	movz w9, #7761, lsl #0
	movk w9, #34, lsl #16
	str w9, [x1, #964]
	movz w9, #27683, lsl #0
	movk w9, #6, lsl #16
	str w9, [x1, #968]
	movz w9, #58103, lsl #0
	movk w9, #34, lsl #16
	str w9, [x1, #972]
	movz w9, #4974, lsl #0
	movk w9, #125, lsl #16
	str w9, [x1, #976]
	movz w9, #59387, lsl #0
	movk w9, #14, lsl #16
	str w9, [x1, #980]
	movz w9, #17367, lsl #0
	movk w9, #103, lsl #16
	str w9, [x1, #984]
	movz w9, #6743, lsl #0
	movk w9, #54, lsl #16
	str w9, [x1, #988]
	movz w9, #30128, lsl #0
	movk w9, #8, lsl #16
	str w9, [x1, #992]
	movz w9, #4309, lsl #0
	movk w9, #68, lsl #16
	str w9, [x1, #996]
	movz w9, #48306, lsl #0
	movk w9, #0, lsl #16
	str w9, [x1, #1000]
	movz w9, #51489, lsl #0
	movk w9, #20, lsl #16
	str w9, [x1, #1004]
	movz w9, #51767, lsl #0
	movk w9, #67, lsl #16
	str w9, [x1, #1008]
	movz w9, #33177, lsl #0
	movk w9, #106, lsl #16
	str w9, [x1, #1012]
	movz w9, #59722, lsl #0
	movk w9, #12, lsl #16
	str w9, [x1, #1016]
	movz w9, #46643, lsl #0
	movk w9, #97, lsl #16
	str w9, [x1, #1020]
	movz w9, #57345, lsl #0
	movk w9, #127, lsl #16
	movz w10, #57343, lsl #0
	movk w10, #64639, lsl #16
	dup v16.4s, w9
	dup v17.4s, w10
	add x2, x0, #0
	add x3, x1, #1020
	movz x5, #32, lsl #0
20:
	ldr q6, [x2, #0]
	ldr q7, [x2, #16]
	sub x3, x3, #12
	ldr q18, [x3, #0]
	rev64 v18.4s, v18.4s
	ext v18.16b, v18.16b, v18.16b, #8
	sub x3, x3, #4
	uzp1 v0.4s, v6.4s, v7.4s
	uzp2 v1.4s, v6.4s, v7.4s
	add v5.4s, v0.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	umull v2.2d, v5.2s, v18.2s
	umull2 v3.2d, v5.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v5.4s, v2.4s, v3.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	zip1 v6.4s, v0.4s, v5.4s
	zip2 v7.4s, v0.4s, v5.4s
	str q6, [x2, #0]
	str q7, [x2, #16]
	add x2, x2, #32
	sub x5, x5, #1
	cbnz x5, 20b
	add x2, x0, #0
	add x3, x1, #508
	movz x5, #32, lsl #0
21:
	ldr q6, [x2, #0]
	ldr q7, [x2, #16]
	sub x3, x3, #4
	ldr q18, [x3, #0]
	zip1 v18.4s, v18.4s, v18.4s
	ext v18.16b, v18.16b, v18.16b, #8
	sub x3, x3, #4
	trn1 v0.2d, v6.2d, v7.2d
	trn2 v1.2d, v6.2d, v7.2d
	add v5.4s, v0.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	umull v2.2d, v5.2s, v18.2s
	umull2 v3.2d, v5.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v5.4s, v2.4s, v3.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	trn1 v6.2d, v0.2d, v5.2d
	trn2 v7.2d, v0.2d, v5.2d
	str q6, [x2, #0]
	str q7, [x2, #16]
	add x2, x2, #32
	sub x5, x5, #1
	cbnz x5, 21b
	add x2, x0, #0
	add x3, x1, #252
	movz x4, #32, lsl #0
22:
	ldr w6, [x3, #0]
	sub x3, x3, #4
	dup v18.4s, w6
	movz x5, #1, lsl #0
23:
	ldr q0, [x2, #0]
	ldr q1, [x2, #16]
	add v5.4s, v0.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	umull v2.2d, v5.2s, v18.2s
	umull2 v3.2d, v5.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v5.4s, v2.4s, v3.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	str q0, [x2, #0]
	str q5, [x2, #16]
	add x2, x2, #16
	sub x5, x5, #1
	cbnz x5, 23b
	add x2, x2, #16
	sub x4, x4, #1
	cbnz x4, 22b
	add x2, x0, #0
	add x3, x1, #124
	movz x4, #16, lsl #0
24:
	ldr w6, [x3, #0]
	sub x3, x3, #4
	dup v18.4s, w6
	movz x5, #2, lsl #0
25:
	ldr q0, [x2, #0]
	ldr q1, [x2, #32]
	add v5.4s, v0.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	umull v2.2d, v5.2s, v18.2s
	umull2 v3.2d, v5.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v5.4s, v2.4s, v3.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	str q0, [x2, #0]
	str q5, [x2, #32]
	add x2, x2, #16
	sub x5, x5, #1
	cbnz x5, 25b
	add x2, x2, #32
	sub x4, x4, #1
	cbnz x4, 24b
	add x2, x0, #0
	add x3, x1, #60
	movz x4, #8, lsl #0
26:
	ldr w6, [x3, #0]
	sub x3, x3, #4
	dup v18.4s, w6
	movz x5, #4, lsl #0
27:
	ldr q0, [x2, #0]
	ldr q1, [x2, #64]
	add v5.4s, v0.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	umull v2.2d, v5.2s, v18.2s
	umull2 v3.2d, v5.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v5.4s, v2.4s, v3.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	str q0, [x2, #0]
	str q5, [x2, #64]
	add x2, x2, #16
	sub x5, x5, #1
	cbnz x5, 27b
	add x2, x2, #64
	sub x4, x4, #1
	cbnz x4, 26b
	add x2, x0, #0
	add x3, x1, #28
	movz x4, #4, lsl #0
28:
	ldr w6, [x3, #0]
	sub x3, x3, #4
	dup v18.4s, w6
	movz x5, #8, lsl #0
29:
	ldr q0, [x2, #0]
	ldr q1, [x2, #128]
	add v5.4s, v0.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	umull v2.2d, v5.2s, v18.2s
	umull2 v3.2d, v5.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v5.4s, v2.4s, v3.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	str q0, [x2, #0]
	str q5, [x2, #128]
	add x2, x2, #16
	sub x5, x5, #1
	cbnz x5, 29b
	add x2, x2, #128
	sub x4, x4, #1
	cbnz x4, 28b
	add x2, x0, #0
	add x3, x1, #12
	movz x4, #2, lsl #0
210:
	ldr w6, [x3, #0]
	sub x3, x3, #4
	dup v18.4s, w6
	movz x5, #16, lsl #0
211:
	ldr q0, [x2, #0]
	ldr q1, [x2, #256]
	add v5.4s, v0.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	umull v2.2d, v5.2s, v18.2s
	umull2 v3.2d, v5.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v5.4s, v2.4s, v3.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	str q0, [x2, #0]
	str q5, [x2, #256]
	add x2, x2, #16
	sub x5, x5, #1
	cbnz x5, 211b
	add x2, x2, #256
	sub x4, x4, #1
	cbnz x4, 210b
	add x2, x0, #0
	add x3, x1, #4
	movz x4, #1, lsl #0
212:
	ldr w6, [x3, #0]
	sub x3, x3, #4
	dup v18.4s, w6
	movz x5, #32, lsl #0
213:
	ldr q0, [x2, #0]
	ldr q1, [x2, #512]
	add v5.4s, v0.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	umull v2.2d, v5.2s, v18.2s
	umull2 v3.2d, v5.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v5.4s, v2.4s, v3.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	str q0, [x2, #0]
	str q5, [x2, #512]
	add x2, x2, #16
	sub x5, x5, #1
	cbnz x5, 213b
	add x2, x2, #512
	sub x4, x4, #1
	cbnz x4, 212b
	movz w6, #16382, lsl #0
	movk w6, #0, lsl #16
	dup v18.4s, w6
	add x2, x0, #0
	movz x5, #64, lsl #0
214:
	ldr q0, [x2, #0]
	umull v2.2d, v0.2s, v18.2s
	umull2 v3.2d, v0.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v0.4s, v2.4s, v3.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	str q0, [x2, #0]
	add x2, x2, #16
	sub x5, x5, #1
	cbnz x5, 214b
	ret
	.p2align 6
