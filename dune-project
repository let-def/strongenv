(lang dune 2.4)

(name strongenv)

(homepage "https://gitea.lakaban.net/def/strongenv")
(bug_reports "https://gitea.lakaban.net/def/strongenv/issues")
; (dev-repo "gitea@gitea.lakaban.net:def/strongenv.git")

(license BSD3)
(authors "Frédéric Bour")
(maintainers "def@lakaban.net")

(package
 (name strongenv)
 (synopsis "An experimental library for typing binding trees")
 (depends
  (grenier (>= 0.14))))

(generate_opam_files)
