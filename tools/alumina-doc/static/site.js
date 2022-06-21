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
        
        window.searchIndex
            .filter(([path, doc, __]) => matcher(path))
            .forEach(([path, doc, href]) => {
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
        
        searchResults.innerText = "";
        searchResults.appendChild(table);
    };


    searchBox.addEventListener("input",  (evt) => {
        clearTimeout(window.debounceTimer);
        window.debounceTimer = setTimeout(window.updateSearchResults, 250);
    });

    window.updateSearchResults();
});