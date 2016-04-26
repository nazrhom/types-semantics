---
title: Theory of Programming and Types
layout: default
---

# Types and Semantics

Welcome to the homepage of *Types and semantics*.


## Latest news

<ul>
  {% for post in site.posts %}
    <li>
      <em> {{ post.date | date_to_string }} </em> <br>
      {{ post.content }}
    </li>
  {% endfor %}
</ul>


