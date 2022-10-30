/*
    Dumps the names of the symbols and fields with associated IDs to JSON.
    This is done because node-types.json does not include numeric IDs, which requires
    the parsing to be done by string names (error-prone and inefficient).
*/

#include <stdio.h>
#include "tree_sitter/parser.h"

extern const TSLanguage *tree_sitter_alumina(void);

int main(void) {
    TSLanguage *language = (TSLanguage *)tree_sitter_alumina();
    printf("{\"fields\":[");
    for (int i = 1; i <= language->field_count; ++i) {
        if (i > 1) {
            printf(",");
        }
        printf("{\"name\":\"%s\",\"id\":%d}", language->field_names[i], i);
    }
    printf("],\"symbols\":[");
    int first = true;
    for (int i = 1; i <= language->symbol_count + 1; ++i) {
        if (language->symbol_metadata[i].visible && language->symbol_metadata[i].named) {
            if (first) {
                first = false;
            } else {
                printf(",");
            }
            printf("{\"name\":\"%s\",\"id\":%d}", language->symbol_names[i], i);
        }
    }
    printf("]}");
}
