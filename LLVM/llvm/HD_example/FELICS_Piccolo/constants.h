/*
 *
 * University of Luxembourg
 * Laboratory of Algorithmics, Cryptology and Security (LACS)
 *
 * FELICS - Fair Evaluation of Lightweight Cryptographic Systems
 *
 * Copyright (C) 2015 University of Luxembourg
 *
 * Written in 2015 by Yann Le Corre <yann.lecorre@uni.lu>
 *
 * This file is part of FELICS.
 *
 * FELICS is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * FELICS is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://www.gnu.org/licenses/>.
 *
 */

#ifndef CONSTANTS_H
#define CONSTANTS_H

//#define PC 1
//#include "data_types.h"
#define CON80_DOUBLE_WORD const uint32_t 
#define SBOX_BYTE const uint8_t
#define GF16_MUL_BYTE const uint8_t

/*
 *
 * Cipher characteristics:
 * 	BLOCK_SIZE - the cipher block size in bytes
 * 	KEY_SIZE - the cipher key size in bytes
 *	ROUND_KEY_SIZE - the cipher round keys size in bytes
 * 	NUMBER_OF_ROUNDS - the cipher number of rounds
 *
 */
#define BLOCK_SIZE 8
#define KEY_SIZE 10
#define ROUND_KEYS_SIZE 108

#define NUMBER_OF_ROUNDS 25

/* Constants for key schedule */
extern CON80_DOUBLE_WORD CON80[];

/* Constants for encryption/decryption */
extern SBOX_BYTE SBOX[];
extern GF16_MUL_BYTE GF16_MUL2[];
extern GF16_MUL_BYTE GF16_MUL3[];
#endif /* CONSTANTS_H */
