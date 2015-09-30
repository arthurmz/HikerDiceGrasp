/*
 * dice.h
 *
 *  Created on: 3 de set de 2015
 *      Author: Arthur
 */

#ifndef DICE_H_
#define DICE_H_

//Configuração inicial: 2,1,3
typedef struct d{
	int bottom, front, right;
	int i, j;
} dice;

dice* new_dice(int diceIPos, int diceJPos);
void copy_values(dice* d1, dice* d2);
int roll_up(dice* d, dice* pai);
int roll_right(dice* d, dice* pai);
int roll_down(dice* d, dice* pai);
int roll_left(dice* d, dice* pai);
int fake_roll_up(dice* d, dice* pai);
int fake_roll_right(dice* d, dice* pai);
int fake_roll_down(dice* d, dice* pai);
int fake_roll_left(dice* d, dice* pai);

#endif /* DICE_H_ */
