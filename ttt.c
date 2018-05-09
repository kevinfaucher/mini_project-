// Victor Kuciel
// Kevin Faucher

//CISC449 - Tic Tac Toe Project

#include <stdlib.h>
#include <ctype.h>
#include <stdio.h>

#define boxArea(box) (box >= 1 && box <= 9 ? TRUE : FALSE)
#define validCoord(x,y) ((x < 0 || x > N-1 || y < 0 || y > N-1) ? FALSE : TRUE)
#define emptyBox(box) (box == ' ' ? TRUE : FALSE)
#define OTHER(player) (player == playerX ? playerO : playerX)
#define playerX 'X'
#define playerO 'O'
#define TRUE 1
#define FALSE 0
#define empty_Space ' '
#define GAMEWIN 1
#define GAMETIE 0
#define GAMELOSE -1
#define INCOMPLETE 2
#define N 3

// **Functions**
void initialize(char board[N][N]);
void print_board(char board[N][N]);
int comp_turn(char board[N][N], char player);
int player_turn(char board[N][N], char player);
int gridTurn(char board[N][N], char player, int grid_var);
int coordTurn(char board[N][N], char player, int x, int y);
int win_check(char board[N][N], char player);
int minNum(char board[N][N], char player);
int maxNum(char board[N][N], char player);
void minimax(char board[N][N], char player); // Use this for the ultimate goal

//
int main() {
        // Board will be [N][N]. N is 3 so the layout will be 3x3
	char board[N][N];

        // Asks user if they want to play as X or O. (X always goes first)
	char selection;

        // Since this game will be played in VirtualBox, ask user in command line
	while(TRUE)
	{
		printf("Play as X? (y/n): ");
		scanf("%c", &selection);
		selection = tolower(selection); // Make lowercase
		if(selection == 'y' || selection == 'n') {
		{
			selection = (selection == 'y' ? playerX : playerO);
			break;
		}
	}
		printf("Wrong selection, try again\n");
	}

	// Initialize the board (need to set them as empty chars)
	initialize(board);
        // Print
	print_board(board);

	while(TRUE)
	{
		if(selection == playerX)
		{
			if(player_turn(board, playerX) == TRUE)
				break;
			if(comp_turn(board, playerO) == TRUE)
				break;
		}else{
			if(comp_turn(board, playerX) == TRUE)
				break;		
			if(player_turn(board, playerO) == TRUE)
				break;
		}
	}

	return 0;
}

// **Function definitions**

// Initialize board
void initialize(char board[N][N]) {
	int i, j;
	for(i=0; i<N; ++i) {
		for(j=0; j<N; ++j) {
			board[i][j] = empty_Space;
		}
	}
}

void print_board(char board[N][N]) {
	printf("\n");
	int i;
	for(i=0; i<N; ++i) {
		printf("| %d | %d | %d |\t\t",1+(N*i),2+(N*i),3+(N*i));

		printf("| %c | %c | %c |\n",board[0][i], board[1][i], board[2][i]);
	}
	printf("\n");
}

// Computer's turn
int comp_turn(char board[N][N], char player) {
	printf("\t\t\tComputer's turn\n");

	minimax(board, player);
	print_board(board);

	int play = win_check(board, player);
	if(play == GAMEWIN) {
		printf("\nWinner is: Computer\n");
		return TRUE;
	}
	else if(play == GAMETIE) {
		printf("\nTie game\n");
		return TRUE;
	}
	return FALSE;
}

// Player's turn
int player_turn(char board[N][N], char player) {
	int grid_var;
	while(TRUE) {
		printf("Enter number: "); // Allows the user to pick a spot according to the diagram
		scanf("%d", &grid_var);
		printf("\t\t\tPlayer's turn\n");	
		if(gridTurn(board, player, grid_var) == 0) // If incorrect location is chosen, make user try again
			break;
	
		printf("Wrong selection, try again\n");
	}
		
	print_board(board);

	int play = win_check(board, player);
	if(play == GAMEWIN) {
		printf("\nYou won\n");
		return TRUE;
	}
	else if(play == GAMETIE) {
		printf("\nTie game\n");
		return TRUE;
	}
	return FALSE;
}

int gridTurn(char board[N][N], char player, int grid_var) {
	if(boxArea(grid_var) == FALSE) {
		return TRUE;
	}
	//Calculates i, j coordinates on grid
	int i,j;
	if(grid_var < 4) {
		j = 0;
	}
	else if(grid_var < 7) {
		j = 1;
	}
	else{
		j = 2;
	}
	i = grid_var-1-(j*N);
	if(emptyBox(board[i][j]) == FALSE) {
		return TRUE;
	}
	board[i][j] = player;

	return FALSE;
}

int coordTurn(char board[N][N], char player, int x, int y) {
	// Check if coordinates are valid
	if(validCoord(x,y) == FALSE) {
		return TRUE;
	}
	if(emptyBox(board[x][y]) == FALSE) {
		return TRUE;
	}
	board[x][y] = player;

	return FALSE;
}

int win_check(char board[N][N], char player) {
	int i, j;
	// For rows and columns
	for(i = 0; i < N; ++i) {
		// Row
		if(board[0][i] != empty_Space) {
			if(board[0][i] == board[1][i] && board[1][i] == board[2][i]) {
				return board[0][i] == player ? GAMEWIN : GAMELOSE;
			}
		}
		// Column
		if(board[i][0] != empty_Space) {
			if(board[i][0] == board[i][1] && board[i][1] == board[i][2]) {
				return board[i][0] == player ? GAMEWIN : GAMELOSE;
			}
		}
	}

	// Check left diagonal
	if(board[0][0] != empty_Space && board[0][0] == board[1][1] && board[1][1] == board[2][2]) {
		return board[0][0] == player ? GAMEWIN : GAMELOSE;
	}

	// Check right diagonal
	if(board[2][0] != empty_Space && board[2][0] == board[1][1] && board[1][1] == board[0][2]) {
		return board[2][0] == player ? GAMEWIN : GAMELOSE;
	}

	// Check for a tie
	for(i = 0; i < N; ++i) {
		for(j = 0; j < N; ++j)
		{
			if(board[i][j] == empty_Space)
				break;
		}
		if(board[i][j] == empty_Space)
			break;
	}
	// Tie
	if(i*j==9)
		return GAMETIE;

	// Incomplete board
	return INCOMPLETE;
}

int minNum(char board[N][N], char player) {
	int result = win_check(board, OTHER(player));
	if(result != INCOMPLETE)
		return result;
	
	int i, j, min;
	min = 10; 
	for(i = 0; i < N; ++i) {
		for(j = 0; j < N; ++j) {
			if(board[i][j] != ' ')
				continue;
			char new_board[N][N];
			int x, y;
			for(x = 0; x < N; ++x) {
				for(y = 0; y < N; ++y) {
					new_board[x][y] = board[x][y];
				}
			}
			if(new_board[i][j] != ' ') {
				printf("minNum error\n"); 
				exit(0);
			}
			new_board[i][j] = player;
			int temp = maxNum(new_board, OTHER(player));
			if(temp < min)
				min = temp;
		}
	}
	return min;
}

int maxNum(char board[N][N], char player) {
	int result = win_check(board, player);
	if(result != INCOMPLETE)
		return result;

	int i, j, max;
	max = -10; 
	for(i = 0; i < N; ++i) {
		for(j = 0; j < N; ++j) {
			if(board[i][j] != ' ')
				continue;
			char new_board[N][N];
			int x, y;
			for(x = 0; x < N; ++x) {
				for(y = 0; y < N; ++y) {
					new_board[x][y] = board[x][y];
				}
			}
			if(new_board[i][j] != ' ') {
				printf("maxNum error\n");
				exit(0);
			}
			new_board[i][j] = player;
			int temp = minNum(new_board, OTHER(player));
			if(temp > max)
				max = temp;
		}
	}
	return max;
}


// The minimax algorithm will achieve the ultimate goal; the computer never loses
void minimax(char board[N][N], char player) {
	int i, j, max, mval_i, mval_j;
	max = -10;
	for(i = 0; i < N; ++i) {
		for(j = 0; j < N; ++j) {
			if(board[i][j] != ' ')
				continue;
			char new_board[N][N];
			int a,b;
			for(a = 0; a < N; ++a) {
				for(b = 0; b < N; ++b) {
					new_board[a][b] = board[a][b];
				}
			}
			new_board[i][j] = player;
			int temp = minNum(new_board, OTHER(player)); // Computer is at top of tree
			if(temp > max) { // Finish with the highest outcome of minNum loop
				max = temp;
				mval_i = i;
				mval_j = j;
			}
		}
	}	
	if(coordTurn(board, player, mval_i, mval_j) == TRUE) {
		printf("Minimax error\n"); 
		exit(0);
	}
}
