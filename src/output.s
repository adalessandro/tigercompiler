	.global _tigermain
L2:
	.word L2.
L2.:
	.long 2
	.ascii " O"
L3:
	.word L3.
L3.:
	.long 2
	.ascii " ."
L9:
	.word L9.
L9.:
	.long 1
	.ascii "\x0a"
L12:
	.word L12.
L12.:
	.long 1
	.ascii "\x0a"
	.align 2
printboard.20.0:
	stmfd   sp!, {r0}
	stmfd   sp!, {fp, lr}
	mov     fp, sp
	sub     sp, sp, #24
	str     r6, [fp, #-24]
	str     r7, [fp, #-4]
	str     r8, [fp, #-8]
	str     r9, [fp, #-12]
	str     r10, [fp, #-16]
	mov     r8, #0
	mov     r0, #0
	mov     r0, #8
	add    r0, r0, fp
	ldr     r0, [r0]
	mov     r1, #4
	sub    r0, r0, r1
	ldr     r0, [r0]
	mov     r1, #1
	sub    r10, r0, r1
L10:
	cmp     r8, r10
	bgt     L0
	b       L11
L11:
	mov     r6, #0
	mov     r0, #0
	mov     r0, #8
	add    r0, r0, fp
	ldr     r0, [r0]
	mov     r1, #4
	sub    r0, r0, r1
	ldr     r0, [r0]
	mov     r1, #1
	sub    r0, r0, r1
	str     r0, [fp, #-20]
L7:
	ldr     r0, [fp, #-20]
	cmp     r6, r0
	bgt     L1
	b       L8
L8:
	mov     r0, #8
	add    r0, r0, fp
	ldr     r0, [r0]
	mov     r1, #12
	sub    r0, r0, r1
	ldr     r7, [r0]
	mov    r0, r7
	mov    r1, r8
	bl      _checkIndexArray
	mov     r0, #4
	mul    r0, r8, r0
	add    r0, r7, r0
	ldr     r0, [r0]
	cmp     r0, r6
	beq     L4
	b       L5
L5:
	ldr     r0, L3
L6:
	bl      print
	mov     r0, #1
	add    r6, r0, r6
	b       L7
L4:
	ldr     r0, L2
	b       L6
L1:
	ldr     r0, L9
	bl      print
	mov     r0, #1
	add    r8, r0, r8
	b       L10
L0:
	ldr     r0, L12
	bl      print
	ldr     r6, [fp, #-24]
	ldr     r7, [fp, #-4]
	ldr     r8, [fp, #-8]
	ldr     r9, [fp, #-12]
	ldr     r10, [fp, #-16]
	b       L31
L31:
	mov     sp, fp
	ldmfd   sp!, {fp, lr}
	add     sp, sp, #4
	bx      lr
	
try.32.1:
	stmfd   sp!, {r0}
	stmfd   sp!, {fp, lr}
	mov     fp, sp
	sub     sp, sp, #32
	str     r6, [fp, #-20]
	str     r8, [fp, #-24]
	str     r10, [fp, #-28]
	str     r1, [fp, #-4]
	mov     r6, #8
	add    r6, r6, fp
	ldr     r6, [r6]
	mov     r3, #4
	sub    r6, r6, r3
	ldr     r6, [r6]
	ldr     r3, [fp, #-4]
	cmp     r3, r6
	beq     L28
	b       L29
L29:
	mov     r6, #0
	str     r6, [fp, #-8]
	mov     r6, #0
	mov     r6, #8
	add    r6, r6, fp
	ldr     r6, [r6]
	mov     r3, #4
	sub    r6, r6, r3
	ldr     r6, [r6]
	mov     r3, #1
	sub    r8, r6, r3
L26:
	ldr     r3, [fp, #-8]
	cmp     r3, r8
	bgt     L13
	b       L27
L27:
	mov     r0, #8
	add    r0, r0, fp
	ldr     r0, [r0]
	mov     r1, #8
	sub    r0, r0, r1
	ldr     r10, [r0]
	ldr     r6, [fp, #-8]
	mov    r0, r10
	mov    r1, r6
	bl      _checkIndexArray
	mov     r2, #4
	mul    r3, r6, r2
	add    r3, r10, r3
	ldr     r3, [r3]
	mov     r2, #0
	cmp     r3, r2
	beq     L16
	b       L17
L17:
	mov     r3, #0
	str     r3, [fp, #-12]
L18:
	mov     r3, #0
	ldr     r2, [fp, #-12]
	cmp     r2, r3
	bne     L21
	b       L22
L22:
	mov     r2, #0
L23:
	mov     r3, #0
	cmp     r2, r3
	bne     L24
	b       L25
L25:
	mov     r3, #1
	ldr     r2, [fp, #-8]
	add    r2, r3, r2
	str     r2, [fp, #-8]
	b       L26
L28:
	mov     r0, #8
	add    r0, r0, fp
	ldr     r0, [r0]
	bl      printboard.20.0
L30:
	ldr     r6, [fp, #-20]
	ldr     r8, [fp, #-24]
	ldr     r10, [fp, #-28]
	b       L33
L16:
	mov     r10, #1
	mov     r0, #8
	add    r0, r0, fp
	ldr     r0, [r0]
	mov     r1, #16
	sub    r0, r0, r1
	ldr     r6, [r0]
	ldr     r0, [fp, #-4]
	ldr     r1, [fp, #-8]
	add    r0, r1, r0
	str     r0, [fp, #-32]
	mov    r0, r6
	ldr     r1, [fp, #-32]
	ldr     r2, [fp, #-32]
	bl      _checkIndexArray
	mov     r2, #4
	ldr     r1, [fp, #-32]
	mul    r2, r1, r2
	add    r3, r6, r2
	ldr     r3, [r3]
	mov     r2, #0
	cmp     r3, r2
	beq     L14
	b       L15
L15:
	mov     r10, #0
L14:
	str     r10, [fp, #-12]
	b       L18
L21:
	mov     r0, #1
	str     r0, [fp, #-16]
	mov     r0, #8
	add    r0, r0, fp
	ldr     r0, [r0]
	mov     r1, #20
	sub    r0, r0, r1
	ldr     r6, [r0]
	mov     r0, #7
	ldr     r1, [fp, #-8]
	add    r0, r1, r0
	ldr     r1, [fp, #-4]
	sub    r10, r0, r1
	mov    r0, r6
	mov    r1, r10
	bl      _checkIndexArray
	mov     r2, #4
	mul    r2, r10, r2
	add    r3, r6, r2
	ldr     r3, [r3]
	mov     r2, #0
	cmp     r3, r2
	beq     L19
	b       L20
L20:
	mov     r3, #0
	str     r3, [fp, #-16]
L19:
	ldr     r2, [fp, #-16]
	b       L23
L24:
	mov     r0, #8
	add    r0, r0, fp
	ldr     r0, [r0]
	mov     r1, #8
	sub    r0, r0, r1
	ldr     r10, [r0]
	ldr     r6, [fp, #-8]
	mov    r0, r10
	mov    r1, r6
	bl      _checkIndexArray
	mov     r0, #4
	mul    r0, r6, r0
	add    r0, r10, r0
	mov     r1, #1
	str     r1, [r0]
	mov     r0, #8
	add    r0, r0, fp
	ldr     r0, [r0]
	mov     r1, #16
	sub    r0, r0, r1
	ldr     r10, [r0]
	ldr     r0, [fp, #-4]
	ldr     r1, [fp, #-8]
	add    r6, r1, r0
	mov    r0, r10
	mov    r1, r6
	bl      _checkIndexArray
	mov     r0, #4
	mul    r0, r6, r0
	add    r0, r10, r0
	mov     r1, #1
	str     r1, [r0]
	mov     r0, #8
	add    r0, r0, fp
	ldr     r0, [r0]
	mov     r1, #20
	sub    r0, r0, r1
	ldr     r10, [r0]
	mov     r0, #7
	ldr     r1, [fp, #-8]
	add    r0, r1, r0
	ldr     r1, [fp, #-4]
	sub    r6, r0, r1
	mov    r0, r10
	mov    r1, r6
	bl      _checkIndexArray
	mov     r0, #4
	mul    r0, r6, r0
	add    r0, r10, r0
	mov     r1, #1
	str     r1, [r0]
	mov     r0, #8
	add    r0, r0, fp
	ldr     r0, [r0]
	mov     r1, #12
	sub    r0, r0, r1
	ldr     r10, [r0]
	ldr     r6, [fp, #-4]
	mov    r0, r10
	mov    r1, r6
	bl      _checkIndexArray
	mov     r0, #4
	mul    r0, r6, r0
	add    r0, r10, r0
	ldr     r1, [fp, #-8]
	str     r1, [r0]
	mov     r0, #1
	ldr     r1, [fp, #-4]
	add    r1, r1, r0
	mov     r0, #8
	add    r0, r0, fp
	ldr     r0, [r0]
	bl      try.32.1
	mov     r0, #8
	add    r0, r0, fp
	ldr     r0, [r0]
	mov     r1, #8
	sub    r0, r0, r1
	ldr     r10, [r0]
	ldr     r6, [fp, #-8]
	mov    r0, r10
	mov    r1, r6
	bl      _checkIndexArray
	mov     r0, #4
	mul    r0, r6, r0
	add    r0, r10, r0
	mov     r1, #0
	str     r1, [r0]
	mov     r0, #8
	add    r0, r0, fp
	ldr     r0, [r0]
	mov     r1, #16
	sub    r0, r0, r1
	ldr     r10, [r0]
	ldr     r0, [fp, #-4]
	ldr     r1, [fp, #-8]
	add    r6, r1, r0
	mov    r0, r10
	mov    r1, r6
	bl      _checkIndexArray
	mov     r0, #4
	mul    r0, r6, r0
	add    r0, r10, r0
	mov     r1, #0
	str     r1, [r0]
	mov     r0, #8
	add    r0, r0, fp
	ldr     r0, [r0]
	mov     r1, #20
	sub    r0, r0, r1
	ldr     r10, [r0]
	mov     r0, #7
	ldr     r1, [fp, #-8]
	add    r0, r1, r0
	ldr     r1, [fp, #-4]
	sub    r6, r0, r1
	mov    r0, r10
	mov    r1, r6
	bl      _checkIndexArray
	mov     r2, #4
	mul    r3, r6, r2
	add    r3, r10, r3
	mov     r2, #0
	str     r2, [r3]
	b       L25
L13:
	b       L30
L33:
	mov     sp, fp
	ldmfd   sp!, {fp, lr}
	add     sp, sp, #4
	bx      lr
	
_tigermain:
	stmfd   sp!, {r0}
	stmfd   sp!, {fp, lr}
	mov     fp, sp
	sub     sp, sp, #24
	str     r10, [fp, #-24]
	mov     r0, #4
	sub    r0, fp, r0
	mov     r1, #8
	str     r1, [r0]
	mov     r0, #8
	sub    r10, fp, r0
	mov     r0, #4
	sub    r0, fp, r0
	ldr     r0, [r0]
	mov     r1, #0
	bl      _allocArray
	str     r0, [r10]
	mov     r0, #12
	sub    r10, fp, r0
	mov     r0, #4
	sub    r0, fp, r0
	ldr     r0, [r0]
	mov     r1, #0
	bl      _allocArray
	str     r0, [r10]
	mov     r0, #16
	sub    r10, fp, r0
	mov     r0, #4
	sub    r0, fp, r0
	ldr     r1, [r0]
	mov     r0, #4
	sub    r0, fp, r0
	ldr     r0, [r0]
	add    r0, r1, r0
	mov     r1, #1
	sub    r0, r0, r1
	mov     r1, #0
	bl      _allocArray
	str     r0, [r10]
	mov     r0, #20
	sub    r10, fp, r0
	mov     r0, #4
	sub    r0, fp, r0
	ldr     r1, [r0]
	mov     r0, #4
	sub    r0, fp, r0
	ldr     r0, [r0]
	add    r0, r1, r0
	mov     r1, #1
	sub    r0, r0, r1
	mov     r1, #0
	bl      _allocArray
	str     r0, [r10]
	mov    r0, fp
	mov     r1, #0
	bl      try.32.1
	mov     r0, #0
	ldr     r10, [fp, #-24]
	b       L35
L35:
	mov     sp, fp
	ldmfd   sp!, {fp, lr}
	add     sp, sp, #4
	bx      lr
	
