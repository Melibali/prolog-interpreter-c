#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h> 

static char *copy_string(const char *s) {
    char *p = malloc(strlen(s) + 1);
    if (!p) { perror("malloc"); exit(1); }
    strcpy(p, s);
    return p;
}
typedef enum { VAR, ATOM, INT } TermType;
typedef struct Term {
    TermType type;
    char *name;
    int value;
    struct Term *liaison;
} Term;

#define MAX_ARGS 10
typedef struct Goal {
    char *pred;              
    Term *args[MAX_ARGS];    
    int nbr_arg;              
    struct Goal *next;      
} Goal;


typedef struct Rule {
    Goal *head;              
    Goal *body;              
    struct Rule *next;
} Rule;

static Rule *kb = NULL;
static Term *trail[1024];
static int trail_top = 0;

static int rename_counter = 0;
static int solve(Goal *goals);

static Term *parse_term(void);
static Goal *parse_goal(void);

static Term *make_var(const char *n) {
    Term *t = malloc(sizeof(Term));
    if (!t) { perror("malloc"); exit(1); }
    t->type = VAR;
    t->name = copy_string(n);
    t->liaison = NULL;
    return t;
}

static Term *make_atom(const char *n) {
    Term *t = malloc(sizeof(Term));
    if (!t) { perror("malloc"); exit(1); }
    t->type = ATOM;
    t->name = copy_string(n);
    t->liaison = NULL;
    return t;
}

static Term *make_int(int v) {
    Term *t = malloc(sizeof(Term));
    if (!t) { perror("malloc"); exit(1); }
    t->type = INT;
    t->value = v;
    t->liaison = NULL;
    t->name = NULL;
    return t;
}
static Term *deref(Term *t) {
    while (t && t->type == VAR && t->liaison != NULL) {
        t = t->liaison;
    }
    return t;
}
static void undo_trail(int saved) {
    while (trail_top > saved) {
        Term *v = trail[--trail_top];
        v->liaison = NULL;
    }
}
static int unify(Term *a, Term *b) {
    a = deref(a);
    b = deref(b);

    if (a->type == VAR) {
        trail[trail_top++] = a;
        a->liaison = b;
        return 1;
    }
    if (b->type == VAR) {
        trail[trail_top++] = b;
        b->liaison = a;
        return 1;

    }
    if (a->type == ATOM && b->type == ATOM) {
        return strcmp(a->name, b->name) == 0;
    }
    if (a->type == INT && b->type == INT) {
        return a->value == b->value;
    }
    return 0;

}

static Term *copy_term(Term *t) {
    t = deref(t);
    if (t->type == VAR) {
        char buf[64];
        sprintf(buf, "%s_%d", t->name, rename_counter);
        return make_var(buf);
    } else if (t->type == ATOM) {
        return make_atom(t->name);
    } else {
        return make_int(t->value);
    }
}



static Goal *copy_goal(Goal *g) {
    if (!g) return NULL;

    Goal *ng = malloc(sizeof(Goal));
    if (!ng) { perror("malloc"); exit(1); }

    ng->pred = copy_string(g->pred);
    ng->nbr_arg = g->nbr_arg;
    ng->next = NULL;
    static Term *vars[32];
    static char *names[32];
    static int var_count = 0;
    static int seen_rename_counter = -1;

   
    if (seen_rename_counter != rename_counter) {
        for (int k = 0; k < 32; k++) {
            vars[k] = NULL;
            names[k] = NULL;
        }
        var_count = 0;
        seen_rename_counter = rename_counter;//permet de réinitialiser la table quand un nouveau cycle de copie commence (rename_counter++)
    }

    for (int i = 0; i < g->nbr_arg; i++) {
        Term *t = deref(g->args[i]);

        if (t->type == VAR) {
            int found = -1;
            for (int j = 0; j < var_count; j++) {
                if (names[j] && strcmp(names[j], t->name) == 0) {
                    found = j;
                    break;
                }
            }

            if (found >= 0) {
                ng->args[i] = vars[found];
            } else {
                char buf[64];
                sprintf(buf, "%s_%d", t->name, rename_counter);
                ng->args[i] = make_var(buf);

                if (var_count < 32) {
                    names[var_count] = t->name;   
                    vars[var_count]  = ng->args[i];
                    var_count++;
                } else {
                    fprintf(stderr, "Trop de variables distinctes dans la règle il faut max 32\n");
                    exit(1);
                }
            }
        } else {
            ng->args[i] = copy_term(t);
        }
    }

    ng->next = copy_goal(g->next);
    return ng;
}
static void write_term(Term *t) {
    t = deref(t);
    if (t->type == VAR) printf("%s", t->name);
    else if (t->type == ATOM) printf("%s", t->name);
    else if (t->type == INT) printf("%d", t->value);
}
static void nl_builtin(void) { printf("\n"); }

static int builtin_write(Goal *g) {
    if (g->nbr_arg == 1) {
        write_term(g->args[0]);
        nl_builtin();
        return 1;
    }
    return 0;
}

static int builtin_nl(Goal *g) {
    if (g->nbr_arg == 0) {
        nl_builtin();
        return 1;
    }
    return 0;
}

static int builtin_is(Goal *g) {
    
    if (g->nbr_arg == 2) {
        Term *x = g->args[0];
        Term *expr = deref(g->args[1]);
        if (expr->type == INT) {
            return unify(x, make_int(expr->value));
        }
    }
    return 0;
}

static int builtin_cut(Goal *g) {
    return 1;
}

static int is_builtin(const char *pred) {
    return strcmp(pred, "write") == 0 ||
           strcmp(pred, "nl") == 0 ||
           strcmp(pred, "is") == 0 ||
           strcmp(pred, "!") == 0;
}

static int call_builtin(Goal *g) {
    if (strcmp(g->pred, "write") == 0) return builtin_write(g);
    if (strcmp(g->pred, "nl") == 0) return builtin_nl(g);
    if (strcmp(g->pred, "is") == 0) return builtin_is(g);
    if (strcmp(g->pred, "!") == 0) return builtin_cut(g);
    return 0;
}


static int solve_with_rule(Goal *g, Rule *r) {
    int saved = trail_top;
    rename_counter++;
    
    Goal *head_copy = copy_goal(r->head);
    Goal *body_copy = copy_goal(r->body);
    
    int match = 1;
    if (strcmp(g->pred, head_copy->pred) != 0 || g->nbr_arg != head_copy->nbr_arg) {
        match = 0;
    } else {
        for (int i = 0; i < g->nbr_arg; i++) {
            if (!unify(g->args[i], head_copy->args[i])) {
                match = 0;
                break;
            }
        }
    }
    
    if (!match) {
        undo_trail(saved);
        return 0;
    }
    
    if (body_copy == NULL) {
        if (g->next) {
            int result = solve(g->next);
            if (!result) undo_trail(saved);
            return result;
        }
        return 1; 
    }
    
    Goal *last = body_copy;
    while (last->next) {
        last = last->next;
    }
    last->next = g->next;
    
    int result = solve(body_copy);
    if (!result) undo_trail(saved);
    return result;
}

static int solve(Goal *goals) {
    if (!goals) return 1; 
    
    Goal *g = goals;
    
    if (is_builtin(g->pred)) {
        if (call_builtin(g)) {
            return solve(g->next);
        }
        return 0;
    }
    
    for (Rule *r = kb; r; r = r->next) {
        if (solve_with_rule(g, r)) {
            return 1; 
        }
    }
    return 0; 
}
static char *input_ptr;

static void skip_spaces(void) {
    while (*input_ptr && isspace(*input_ptr)) input_ptr++;
}

static Term *parse_term(void) {
    skip_spaces();
    
    if (isupper(*input_ptr) || *input_ptr == '_') {
        char name[64];
        int i = 0;
        while (isalnum(*input_ptr) || *input_ptr == '_') {
            name[i++] = *input_ptr++;
        }
        name[i] = '\0';
        return make_var(name);
    }
    
    if (isdigit(*input_ptr)) {
        int val = 0;
        while (isdigit(*input_ptr)) {
            val = val * 10 + (*input_ptr++ - '0');
        }
        return make_int(val);
    }
        if (islower(*input_ptr)) {
        char name[64];
        int i = 0;
        while (isalnum(*input_ptr) || *input_ptr == '_') {
            name[i++] = *input_ptr++;
        }
        name[i] = '\0';
        return make_atom(name);
    }
    
    return NULL;
}

static Goal *parse_goal(void) {
    skip_spaces();
    
    char pred[64];
    int i = 0;
    if (*input_ptr == '!') {
        input_ptr++;
        Goal *g = malloc(sizeof(Goal));
        g->pred = copy_string("!");
        g->nbr_arg = 0;
        g->next = NULL;
        return g;
    }
    if (!islower(*input_ptr)) return NULL;
    
    while (isalnum(*input_ptr) || *input_ptr == '_') {
        pred[i++] = *input_ptr++;
    }
    pred[i] = '\0';
    
    skip_spaces();
    
    Goal *g = malloc(sizeof(Goal));
    g->pred = copy_string(pred);
    g->nbr_arg = 0;
    g->next = NULL;
        if (*input_ptr == '(') {
        input_ptr++;
        skip_spaces();
        
        while (*input_ptr && *input_ptr != ')') {
            Term *arg = parse_term();
            if (!arg) break;
            g->args[g->nbr_arg++] = arg;
            
            skip_spaces();
            if (*input_ptr == ',') {
                input_ptr++;
            }
        }
        
        if (*input_ptr == ')') input_ptr++;
    }
    
    return g;
}

static Goal *parse_query(const char *query) {
    input_ptr = (char*)query;
    Goal *first = NULL, *last = NULL;
    while (*input_ptr) {
        skip_spaces();
        if (!*input_ptr) break;
        
        Goal *g = parse_goal();
        if (!g) break;
        
        if (!first) {
            first = last = g;
        } else {
            last->next = g;
            last = g;
        }
        
        skip_spaces();
        if (*input_ptr == ',') {
            input_ptr++;
        } else if (*input_ptr == '.') {
            input_ptr++;
            break;
        }
    }
    
    return first;
}

static void add_fact(const char *pred, const char *a, const char *b) {
    Rule *r = malloc(sizeof(Rule));
    r->head = malloc(sizeof(Goal));
    r->head->pred = copy_string(pred);
    r->head->nbr_arg = 2;
    r->head->args[0] = make_atom(a);
    r->head->args[1] = make_atom(b);
    r->head->next = NULL;
    r->body = NULL;
    r->next = kb;
    kb = r;
}
static void add_rule(Goal *head, Goal *body) {
    Rule *r = malloc(sizeof(Rule));
    r->head = head;
    r->body = body;
    r->next = kb;
    kb = r;
}
int main(void) {

    /* Base de connaissances */

    add_fact("parent", "john", "mary");
    add_fact("parent", "mary", "susan");
    add_fact("parent","susan","jacques");
    add_fact("parent","jacques","jean");
    

    Goal *gp_head = malloc(sizeof(Goal));

    gp_head->pred = copy_string("grandparent");
    gp_head->nbr_arg = 2;
    gp_head->args[0] = make_var("X");
    gp_head->args[1] = make_var("Z");
    gp_head->next = NULL;               

    Goal *gp_body1 = malloc(sizeof(Goal));

    gp_body1->pred = copy_string("parent");

    gp_body1->nbr_arg = 2;

    gp_body1->args[0] = make_var("X");

    gp_body1->args[1] = make_var("Y");

   

    Goal *gp_body2 = malloc(sizeof(Goal));

    gp_body2->pred = copy_string("parent");

    gp_body2->nbr_arg = 2;

    gp_body2->args[0] = make_var("Y");
    gp_body2->args[1] = make_var("Z");

    gp_body2->next = NULL;

   

    gp_body1->next = gp_body2;

    add_rule(gp_head, gp_body1);

    gp_head = malloc(sizeof(Goal));

    gp_head->pred = copy_string("ancetre");
    gp_head->nbr_arg = 2;
    gp_head->args[0] = make_var("X");
    gp_head->args[1] = make_var("Y");
    gp_head->next = NULL;               

    gp_body1 = malloc(sizeof(Goal));

    gp_body1->pred = copy_string("parent");

    gp_body1->nbr_arg = 2;

    gp_body1->args[0] = make_var("X");

    gp_body1->args[1] = make_var("Z");

   

    gp_body2 = malloc(sizeof(Goal));

    gp_body2->pred = copy_string("ancetre");

    gp_body2->nbr_arg = 2;

    gp_body2->args[0] = make_var("Z");
    gp_body2->args[1] = make_var("Y");

    gp_body2->next = NULL;

   

    gp_body1->next = gp_body2;

    add_rule(gp_head, gp_body1);


    gp_head = malloc(sizeof(Goal));

    gp_head->pred = copy_string("ancetre");
    gp_head->nbr_arg = 2;
    gp_head->args[0] = make_var("X");
    gp_head->args[1] = make_var("Y");
    gp_head->next = NULL;               

    gp_body1 = malloc(sizeof(Goal));



    gp_head = malloc(sizeof(Goal));

    gp_head->pred = copy_string("ancetre");
    gp_head->nbr_arg = 2;
    gp_head->args[0] = make_var("X");
    gp_head->args[1] = make_var("Y");
    gp_head->next = NULL;               

    gp_body1 = malloc(sizeof(Goal));

    gp_body1->pred = copy_string("parent");

    gp_body1->nbr_arg = 2;

    gp_body1->args[0] = make_var("X");

    gp_body1->args[1] = make_var("Y");
    gp_body1->next = NULL;               

    add_rule(gp_head, gp_body1);

   
    printf("Interpréteur Prolog \n");
    printf("Exemples de requêtes :\n");
    printf("  parent(X, Y), write(X), nl.\n");
    printf("  grandparent(john,susan), write(X), nl.\n");
    printf("Tapez 'quit' pour quitter.\n\n");

   

    char query[256];

    while (1) {

        printf("?- ");

        if (!fgets(query, sizeof(query), stdin)) break;
        if (strncmp(query, "quit", 4) == 0) break;
        Goal *goals = parse_query(query);

        if (!goals) {
            printf("Erreur de parsing.\n");
            continue;
        }
        trail_top = 0;

        if (solve(goals)) {

            printf("true.\n");

        } else {

            printf("false.\n");
        }

    }
    return 0;
}