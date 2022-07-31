window.updateSearchResults = () => {};
window.loadSearchIndex = (idx) => {
    window.searchIndex = idx;
    window.updateSearchResults();
};
window.debounceTimer = null;
window.addEventListener("load", () => {
    const mainContent = document.getElementById("main-content");
    const searchResults = document.getElementById("search-results");
    const searchBox = document.getElementById("search-input");

    const queryParams = new URLSearchParams(window.location.search);
    const initialSearch = queryParams.get("q");
    if (initialSearch) {
        searchBox.value = initialSearch;
    }

    window.updateSearchResults = () => {
        if (searchBox.value !== "") {
            searchResults.style.display = 'block';
            mainContent.style.display = 'none';
        } else {
            searchResults.style.display = 'none';
            mainContent.style.display = 'block';
            return;
        }

        if (!window.searchIndex) {
            searchResults.innerText = "Loading search index...";
            return;
        }

        const table = document.createElement("div");
        table.className = "search-results-table";

        const needles = searchBox.value.split(" ")
            .map(s => s.trim().toLowerCase())
            .filter(s => !!s);

        const matcher = (s) => {
            const haystack = s.toLowerCase();
            for (var index = 0; index < needles.length; index++) {
                if (!haystack.includes(needles[index])) {
                    return false;
                }
            }
            return true;
        };

        const results = window.searchIndex
            .filter(([path, doc, __]) => matcher(path));

        // Put the exact matches to the top
        const exactMatchSuffix = `::${searchBox.value}`.toLowerCase();
        const exactMatcher = (s) => s === searchBox.value || s.toLowerCase().endsWith(exactMatchSuffix);

        results.sort(([a, _, __], [b, ___, ____]) => {
            if (exactMatcher(a) ^ exactMatcher(b)) {
                return exactMatcher(a) ? -1 : 1
            } else {
                return 0
            }
        });

        const hasMore = results.splice(500).length > 0;
        results.forEach(([path, doc, href]) => {
            const child = document.createElement("div");
            child.className = "row";
            const pathCell = document.createElement("div");
            pathCell.className = "cell-name";
            const link = document.createElement("a");
            link.href = href;
            link.innerText = path;
            pathCell.appendChild(link);
            const docCell = document.createElement("div");
            docCell.className = "cell-doc";
            docCell.innerText = doc;
            child.appendChild(pathCell);
            child.appendChild(docCell);
            table.appendChild(child);
        });

        if (table.children.length == 0) {
            searchResults.innerText = "No results";
        } else {
            searchResults.innerText = "";
            searchResults.appendChild(table);
            if (hasMore) {
                searchResults.appendChild(document.createTextNode("More found, refine your search."));
            }
        }
    };


    searchBox.addEventListener("input",  (evt) => {
        clearTimeout(window.debounceTimer);
        if (searchBox.value) {
            history.replaceState(null, null, `?q=${encodeURIComponent(searchBox.value)}`);
            window.debounceTimer = setTimeout(window.updateSearchResults, 200);
        } else {
            history.replaceState(null, null, window.location.href.split("?")[0]);
            window.updateSearchResults();
        }
    });

    window.updateSearchResults();
});
