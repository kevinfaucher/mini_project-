
#include <stdlib.h>
#include <ctype.h>
#include <stdio.h>
#include <stdbool.h>

#define boxArea(box) (box >= 1 && box <= 9 ? TRUE : FALSE)
#define validCoord(x, y) ((x < 0 || x > N-1 || y < 0 || y > N-1) ? FALSE : TRUE)
#define emptyBox(box) (box == ' ' ? TRUE : FALSE)
#define OTHER(player) (player == playerX ? playerO : playerX)
#define playerX 'X'
#define playerO 'O'
#define TRUE 1
#define FALSE 0
#define open_spot ' '
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

int tie_check(char board[N][N]);

int minNum(char board[N][N], char player);

int maxNum(char board[N][N], char player);

void minimax(char board[N][N], char player);

bool end_game(int play);

int main() {
    
    char board[N][N];
    initialize(board);
    print_board(board);
    while (TRUE) {
        if (player_turn(board, playerX) == TRUE)
            break;
        if (comp_turn(board, playerO) == TRUE)
            break;
    }
    return 0;
}


// Initialize board

/*@
  @ requires \valid(board[0..(N-1)]+(0..2));
  @ ensures \forall int i, j; 0<=j<i<2 ==> board[i][j] == open_spot;
  @*/
void initialize(char board[N][N]) {
    int i, j;
    /*@
	  @ loop invariant 0<=j<=i<=N;
	  @ loop invariant \forall int i,j; 0<=j<i<N ==> board[i][j] == open_spot;
	  @ loop assigns i,j;
	  @*/
    for (i = 0; i < N; ++i) {
        for (j = 0; j < N; ++j) {
            board[i][j] = open_spot;
        }
    }
}

void print_board(char board[N][N]) {
    //printf("\n");
    int i;
    for (i = 0; i < N; ++i) {
        //printf("| %c | %c | %c |\n", board[0][i], board[1][i], board[2][i]);
    }
    //printf("\n");
}

/*@
  @ requires \true;
  @ assigns \nothing;
  @*/
bool end_game(int play) {
    if (play == GAMEWIN) {
        //printf("\nWinner is: Computer\n");
        return TRUE;
    } else if (play == GAMETIE) {
        //printf("\nTie game\n");
        return TRUE;
    }
    return FALSE;

}


int comp_turn(char board[N][N], char player) {
    //printf("\t\t\tComputer's turn\n");

    minimax(board, player);
    print_board(board);

    int play = win_check(board, player);
    return end_game(play);

}

// Player's turn
int player_turn(char board[N][N], char player) {
    int grid_var;
    while (TRUE) {
        //printf("Enter number: "); // Allows the user to pick a spot according to the diagram
        //scanf("%d", &grid_var);
        //printf("\t\t\tPlayer's turn\n");
        if (gridTurn(board, player, grid_var) == 0) // If incorrect location is chosen, make user try again
            break;

        //printf("Wrong selection, try again\n");
    }

    print_board(board);

    int play = win_check(board, player);
    return end_game(play);
}

int gridTurn(char board[N][N], char player, int grid_var) {
    if (boxArea(grid_var) == FALSE) {
        return TRUE;
    }
    //Calculates i, j coordinates on grid
    int i, j;
    if (grid_var < 4) {
        j = 0;
    } else if (grid_var < 7) {
        j = 1;
    } else {
        j = 2;
    }
    i = grid_var - 1 - (j * N);
    if (emptyBox(board[i][j]) == FALSE) {
        return TRUE;
    }
    board[i][j] = player;

    return FALSE;
}

int coordTurn(char board[N][N], char player, int x, int y) {
    // Check if coordinates are valid
    if (validCoord(x, y) == FALSE) {
        return TRUE;
    }
    if (emptyBox(board[x][y]) == FALSE) {
        return TRUE;
    }
    board[x][y] = player;

    return FALSE;
}


int win_check(char board[N][N], char player) {
    int i, j;
    // For rows and columns
    for (i = 0; i < N; ++i) {
        // Row
        if (board[0][i] != open_spot) {
            if (board[0][i] == board[1][i] && board[1][i] == board[2][i]) {
                return board[0][i] == player ? GAMEWIN : GAMELOSE;
            }
        }
        // Column
        if (board[i][0] != open_spot) {
            if (board[i][0] == board[i][1] && board[i][1] == board[i][2]) {
                return board[i][0] == player ? GAMEWIN : GAMELOSE;
            }
        }
    }

    // Check left diagonal
    if (board[0][0] != open_spot && board[0][0] == board[1][1] && board[1][1] == board[2][2]) {
        return board[0][0] == player ? GAMEWIN : GAMELOSE;
    }

    // Check right diagonal
    if (board[2][0] != open_spot && board[2][0] == board[1][1] && board[1][1] == board[0][2]) {
        return board[2][0] == player ? GAMEWIN : GAMELOSE;
    }
	
	// check for a tie
    return tie_check(board);

}


int tie_check(char board[N][N]){
    // Check for a tie
    int i, j;
    for ( i = 0; i < N; ++i) {
        for ( j = 0; j < N; ++j) {
            if (board[i][j] == open_spot)
                break;
        }
        if (board[i][j] == open_spot)
            break;
    }
    // Tie
    if (i * j == 9)
        return GAMETIE;
        
    // Incomplete board
    return INCOMPLETE;

}


int minNum(char board[N][N], char player) {
    int result = win_check(board, OTHER(player));
    if (result != INCOMPLETE)
        return result;

    int i, j, min;
    min = 10;
    for (i = 0; i < N; ++i) {
        for (j = 0; j < N; ++j) {
            if (board[i][j] != ' ')
                continue;
            char new_board[N][N];
            int x, y;
            for (x = 0; x < N; ++x) {
                for (y = 0; y < N; ++y) {
                    new_board[x][y] = board[x][y];
                }
            }
            if (new_board[i][j] != ' ') {
                //printf("minNum error\n");
                exit(0);
            }
            new_board[i][j] = player;
            int temp = maxNum(new_board, OTHER(player));
            if (temp < min)
                min = temp;
        }
    }
    return min;
}

int maxNum(char board[N][N], char player) {
    int result = win_check(board, player);
    if (result != INCOMPLETE)
        return result;

    int i, j, max;
    max = -10;
    for (i = 0; i < N; ++i) {
        for (j = 0; j < N; ++j) {
            if (board[i][j] != ' ')
                continue;
            char new_board[N][N];
            int x, y;
            for (x = 0; x < N; ++x) {
                for (y = 0; y < N; ++y) {
                    new_board[x][y] = board[x][y];
                }
            }
            if (new_board[i][j] != ' ') {
                //printf("maxNum error\n");
                exit(0);
            }
            new_board[i][j] = player;
            int temp = minNum(new_board, OTHER(player));
            if (temp > max)
                max = temp;
        }
    }
    return max;
}


void minimax(char board[N][N], char player) {
    int i, j, max, mval_i, mval_j;
    max = -10;
    for (i = 0; i < N; ++i) {
        for (j = 0; j < N; ++j) {
            if (board[i][j] != ' ')
                continue;
            char new_board[N][N];
            int a, b;
            for (a = 0; a < N; ++a) {
                for (b = 0; b < N; ++b) {
                    new_board[a][b] = board[a][b];
                }
            }
            new_board[i][j] = player;
            int temp = minNum(new_board, OTHER(player)); // Computer is at top of tree
            if (temp > max) { // Finish with the highest outcome of minNum loop
                max = temp;
                mval_i = i;
                mval_j = j;
            }
        }
    }
    if (coordTurn(board, player, mval_i, mval_j) == TRUE) {
        //printf("Minimax error\n");
        exit(0);
    }
}
